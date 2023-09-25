// Copyright 2023 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     https://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std::collections::HashMap;
use std::iter::Iterator;
use std::rc::Rc;

use anyhow::bail;
use anyhow::Context;

pub use crate::btree::*;
use crate::pager::PageId;
use crate::pager::ROOT_PAGE_ID;
use crate::parser::expect_no_more_token;
use crate::parser::parse_create_index;
use crate::parser::parse_create_table;
use crate::parser::ColumnConstraint;
use crate::parser::Parser;
use crate::utils::upper_to_lower;
use crate::utils::CaseInsensitiveBytes;
use crate::utils::MaybeQuotedBytes;
use crate::utils::UPPER_TO_LOWER;
use crate::value::Collation;
use crate::value::TypeAffinity;
use crate::value::Value;
use crate::value::DEFAULT_COLLATION;
use crate::Columns;
use crate::Statement;

struct SchemaRecord<'a> {
    type_: &'a [u8],
    name: &'a [u8],
    table_name: &'a [u8],
    root_page_id: u32,
    sql: Option<&'a [u8]>,
}

impl<'a> SchemaRecord<'a> {
    fn parse(columns: &'a Columns<'a>) -> anyhow::Result<Self> {
        let Value::Text(type_) = columns.get(0) else {
            bail!("invalid type: {:?}", columns.get(0));
        };

        let Value::Text(name) = columns.get(1) else {
            bail!("invalid name: {:?}", columns.get(1));
        };

        let Value::Text(table_name) = columns.get(2) else {
            bail!("invalid tbl_name: {:?}", columns.get(2));
        };

        let Value::Integer(root_page_id) = columns.get(3) else {
            bail!("invalid root_page_id: {:?}", columns.get(3));
        };
        let root_page_id = (*root_page_id).try_into().context("parse root_page_id")?;

        let sql: Option<&[u8]> = match columns.get(4) {
            Value::Null => None,
            Value::Text(sql) => Some(sql),
            _ => bail!("invalid sql: {:?}", columns.get(4)),
        };
        Ok(Self {
            type_,
            name,
            table_name,
            root_page_id,
            sql,
        })
    }
}

pub struct Schema {
    schema_table: Table,
    // TODO: Use the reference of table name in the value as the key.
    tables: HashMap<Vec<u8>, Table>,
    indexes: HashMap<Vec<u8>, Rc<Index>>,
}

impl Schema {
    pub fn schema_table() -> Table {
        Table {
            root_page_id: ROOT_PAGE_ID,
            columns: vec![
                Column {
                    name: b"type".to_vec(),
                    type_affinity: TypeAffinity::Text,
                    primary_key: false,
                    collation: Collation::Binary,
                },
                Column {
                    name: b"name".to_vec(),
                    type_affinity: TypeAffinity::Text,
                    primary_key: false,
                    collation: Collation::Binary,
                },
                Column {
                    name: b"tbl_name".to_vec(),
                    type_affinity: TypeAffinity::Text,
                    primary_key: false,
                    collation: Collation::Binary,
                },
                Column {
                    name: b"rootpage".to_vec(),
                    type_affinity: TypeAffinity::Integer,
                    primary_key: false,
                    collation: Collation::Binary,
                },
                Column {
                    name: b"sql".to_vec(),
                    type_affinity: TypeAffinity::Text,
                    primary_key: false,
                    collation: Collation::Binary,
                },
            ],
            indexes: None,
        }
    }

    pub fn generate(stmt: Statement, schema_table: Table) -> anyhow::Result<Schema> {
        let mut stmt = stmt;
        let mut rows = stmt.execute()?;
        let mut tables = HashMap::new();
        let mut indexes = HashMap::new();
        while let Some(row) = rows.next_row()? {
            let columns = row.parse()?;
            let schema = SchemaRecord::parse(&columns)?;
            match schema.type_ {
                b"table" => {
                    if schema.name != schema.table_name {
                        bail!(
                            "table name does not match: name={:?}, table_name={:?}",
                            schema.name,
                            schema.table_name
                        );
                    }
                    let (mut table_name, table) = Table::parse(
                        schema
                            .sql
                            .ok_or(anyhow::anyhow!("no sql for table schema"))?,
                        schema.root_page_id,
                    )
                    .context("parse create table sql")?;
                    if table_name != schema.name {
                        bail!(
                            "table name does not match: table_name={:?}, parsed_table_name={:?}",
                            schema.table_name,
                            table_name
                        );
                    }
                    upper_to_lower(&mut table_name);
                    tables.insert(table_name, table);
                }
                b"index" => {
                    // schema.table_name is the same as the schema.name of the table entry.
                    let mut table_name = schema.table_name.to_vec();
                    upper_to_lower(&mut table_name);
                    let table = tables
                        .get_mut(&table_name)
                        .context("index table not found")?;
                    // TODO: validate the schema.table is equal to table.name.
                    if let Some(sql) = schema.sql {
                        let (mut index_name, parsed_table_name, mut index) =
                            Index::parse(sql, schema.root_page_id, table)?;
                        if index_name != schema.name {
                            bail!(
                                "index name does not match: index_name={:?}, parsed_index_name={:?}",
                                schema.name,
                                index_name
                            );
                        } else if !table_name.as_slice().iter().eq(parsed_table_name
                            .dequote_iter()
                            .map(|v| &UPPER_TO_LOWER[*v as usize]))
                        {
                            bail!(
                                "index table name does not match: table_name={:?}, parsed_table_name={:?}",
                                schema.table_name,
                                parsed_table_name
                            );
                        }
                        index.next = table.indexes.clone();
                        let index = Rc::new(index);
                        table.indexes = Some(index.clone());

                        upper_to_lower(&mut index_name);
                        indexes.insert(index_name, index);
                    } else {
                        // TODO: support autoindex
                        eprintln!("no sql for index: {:?}", schema.name);
                    }
                }
                b"view" => {
                    // TODO: support view
                }
                b"trigger" => {
                    // TODO: support trigger
                }
                type_ => bail!("unsupported type: {:?}", type_),
            }
        }
        Ok(Self {
            schema_table,
            tables,
            indexes,
        })
    }

    pub fn get_table(&self, table: &[u8]) -> Option<&Table> {
        // TODO: use the reference of given table name.
        let mut key = table.to_vec();
        upper_to_lower(&mut key);
        if key == b"sqlite_schema" {
            Some(&self.schema_table)
        } else {
            self.tables.get(&key)
        }
    }

    #[allow(unused)]
    pub fn get_index(&self, index: &[u8]) -> Option<&Rc<Index>> {
        // TODO: use the reference of given index name.
        let mut key = index.to_vec();
        upper_to_lower(&mut key);
        self.indexes.get(&key)
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Index {
    pub root_page_id: PageId,
    pub columns: Vec<ColumnNumber>,
    pub next: Option<Rc<Index>>,
}

impl Index {
    fn parse<'a>(
        sql: &'a [u8],
        root_page_id: PageId,
        table: &Table,
    ) -> anyhow::Result<(Vec<u8>, MaybeQuotedBytes<'a>, Self)> {
        let mut parser = Parser::new(sql);
        let create_index = parse_create_index(&mut parser)
            .map_err(|e| anyhow::anyhow!("parse create index sql: {:?}", e))?;
        if expect_no_more_token(&mut parser).is_err() {
            bail!(
                "create table sql in sqlite_schema contains useless contents at the tail: {:?}",
                sql
            );
        }
        let mut columns = Vec::with_capacity(create_index.columns.len());
        for column in &create_index.columns {
            // TODO: use the reference of given column name.
            let column_name = column.name.dequote();
            let Some((column_number, _, _)) = table.get_column(&column_name) else {
                bail!(
                    "column {:?} in create index sql is not found in table {:?}",
                    column.name,
                    table
                );
            };
            columns.push(column_number);
        }
        Ok((
            create_index.index_name.dequote(),
            create_index.table_name,
            Self {
                root_page_id,
                columns,
                next: None,
            },
        ))
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Column {
    pub name: Vec<u8>,
    pub type_affinity: TypeAffinity,
    pub primary_key: bool,
    pub collation: Collation,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ColumnNumber {
    RowId,
    Column(usize),
}

/// Convert type name (which is a identifier sequence) to type affinity.
///
/// https://www.sqlite.org/datatype3.html#determination_of_column_affinity
pub fn calc_type_affinity(type_name: &[MaybeQuotedBytes]) -> TypeAffinity {
    if type_name.is_empty() {
        return TypeAffinity::Blob;
    }
    let mut affinity = TypeAffinity::Numeric;
    for name in type_name {
        let data_type = CaseInsensitiveBytes::from(name.raw());
        if data_type.contains_lower_bytes(b"int") {
            return TypeAffinity::Integer;
        } else if data_type.contains_lower_bytes(b"char")
            || data_type.contains_lower_bytes(b"clob")
            || data_type.contains_lower_bytes(b"text")
        {
            affinity = TypeAffinity::Text;
        } else if data_type.contains_lower_bytes(b"blob") {
            if affinity != TypeAffinity::Text {
                affinity = TypeAffinity::Blob;
            }
        } else if affinity == TypeAffinity::Numeric
            && (data_type.contains_lower_bytes(b"real")
                || data_type.contains_lower_bytes(b"floa")
                || data_type.contains_lower_bytes(b"doub"))
        {
            affinity = TypeAffinity::Real;
        }
    }
    affinity
}

/// Parse the collation name to [Collation].
///
/// This now supports BINARY, NOCASE, and RTRIM only.
///
/// TODO: Support user defined collating sequence.
pub fn calc_collation(collation_name: &MaybeQuotedBytes) -> anyhow::Result<Collation> {
    // TODO: Validate with iterator.
    let collation_name = collation_name.dequote();
    let case_insensitive_collation_name = CaseInsensitiveBytes::from(collation_name.as_slice());
    if case_insensitive_collation_name.equal_to_lower_bytes(b"binary") {
        Ok(Collation::Binary)
    } else if case_insensitive_collation_name.equal_to_lower_bytes(b"nocase") {
        Ok(Collation::NoCase)
    } else if case_insensitive_collation_name.equal_to_lower_bytes(b"rtrim") {
        Ok(Collation::RTrim)
    } else {
        bail!("invalid collation: {:?}", collation_name);
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Table {
    pub root_page_id: PageId,
    pub columns: Vec<Column>,
    pub indexes: Option<Rc<Index>>,
}

impl Table {
    fn parse(sql: &[u8], root_page_id: PageId) -> anyhow::Result<(Vec<u8>, Self)> {
        let mut parser = Parser::new(sql);
        let create_table = parse_create_table(&mut parser)
            .map_err(|e| anyhow::anyhow!("parse create table sql: {:?}", e))?;
        if expect_no_more_token(&mut parser).is_err() {
            bail!(
                "create table sql in sqlite_schema contains useless contents at the tail: {:?}",
                sql
            );
        }
        let table_name = create_table.table_name.dequote();
        let mut columns: Vec<Column> = Vec::with_capacity(create_table.columns.len());
        let mut has_primary_key = false;
        for column_def in create_table.columns {
            let column_name = column_def.name.dequote();
            let case_insensitive_name = CaseInsensitiveBytes::from(&column_name);
            // TODO: Optimize validation (e.g. hashset)
            for column in &columns {
                if CaseInsensitiveBytes::from(&column.name) == case_insensitive_name {
                    bail!("duplicate column name: {:?}", column_def.name);
                }
            }

            let primary_key = column_def
                .constraints
                .contains(&ColumnConstraint::PrinaryKey);
            if primary_key {
                if has_primary_key {
                    bail!("multiple primary key");
                }
                has_primary_key = true;
            }

            let mut collation = DEFAULT_COLLATION.clone();
            for constraint in &column_def.constraints {
                if let ColumnConstraint::Collate(collation_name) = constraint {
                    collation = calc_collation(collation_name)?;
                }
            }

            columns.push(Column {
                name: column_name,
                type_affinity: calc_type_affinity(&column_def.type_name),
                primary_key,
                collation,
            });
        }
        Ok((
            table_name,
            Table {
                root_page_id,
                columns,
                indexes: None,
            },
        ))
    }

    pub fn get_column(&self, name: &[u8]) -> Option<(ColumnNumber, TypeAffinity, Collation)> {
        let column = CaseInsensitiveBytes::from(name);
        if let Some((i, column)) = self
            .columns
            .iter()
            .enumerate()
            .find(|(_, c)| CaseInsensitiveBytes::from(&c.name) == column)
        {
            let column_number =
                if column.primary_key && column.type_affinity == TypeAffinity::Integer {
                    ColumnNumber::RowId
                } else {
                    ColumnNumber::Column(i)
                };
            Some((
                column_number,
                column.type_affinity,
                column.collation.clone(),
            ))
        } else if column.equal_to_lower_bytes(b"rowid".as_slice()) {
            Some((
                ColumnNumber::RowId,
                TypeAffinity::Integer,
                DEFAULT_COLLATION.clone(),
            ))
        } else {
            None
        }
    }

    pub fn get_all_columns(
        &self,
    ) -> impl Iterator<Item = (ColumnNumber, TypeAffinity, Collation)> + '_ {
        self.columns.iter().enumerate().map(|(i, column)| {
            if column.primary_key && column.type_affinity == TypeAffinity::Integer {
                (
                    ColumnNumber::RowId,
                    TypeAffinity::Integer,
                    column.collation.clone(),
                )
            } else {
                (
                    ColumnNumber::Column(i),
                    column.type_affinity,
                    column.collation.clone(),
                )
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;
    use crate::test_utils::*;
    use crate::Connection;
    use crate::Expression;

    fn generate_schema(filepath: &Path) -> Schema {
        let mut conn = Connection::open(filepath).unwrap();
        let schema_table = Schema::schema_table();
        let columns = schema_table
            .get_all_columns()
            .map(Expression::Column)
            .collect::<Vec<_>>();
        Schema::generate(
            Statement::new(&mut conn, schema_table.root_page_id, columns, None),
            schema_table,
        )
        .unwrap()
    }

    #[test]
    fn get_table_page_id_success() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE TABLE example2(col1, col2);",
            "CREATE TABLE example3(col1, col2, col3);",
        ]);
        let schema = generate_schema(file.path());

        assert_eq!(schema.get_table(b"example2").unwrap().root_page_id, 3);
    }

    #[test]
    fn get_table_page_id_interior_success() {
        let mut queries = Vec::with_capacity(100);
        for i in 0..100 {
            queries.push(format!(
                "CREATE TABLE example{i}(col1,col2,col3,col4,col5,col6,col7,col8,col9,col10);"
            ));
        }
        let file =
            create_sqlite_database(&queries.iter().map(|q| q.as_str()).collect::<Vec<&str>>());
        let pager = create_pager(file.as_file().try_clone().unwrap()).unwrap();
        let schema = generate_schema(file.path());

        assert!(pager.num_pages() > 1);
        assert_eq!(schema.get_table(b"example99").unwrap().root_page_id, 104);
    }

    #[test]
    fn get_table_page_id_sqlite_schema() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE TABLE example2(col1, col2);",
            "CREATE TABLE example3(col1, col2, col3);",
        ]);
        let schema = generate_schema(file.path());

        assert_eq!(
            schema.get_table(b"sqlite_schema").unwrap().root_page_id,
            ROOT_PAGE_ID
        );
    }

    #[test]
    fn get_table_case_insensitive() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE TABLE exAmple2(col1, col2);",
            "CREATE TABLE example3(col1, col2, col3);",
        ]);
        let schema = generate_schema(file.path());

        assert_eq!(schema.get_table(b"example2").unwrap().root_page_id, 3);
        assert_eq!(schema.get_table(b"exaMple2").unwrap().root_page_id, 3);
        assert_eq!(
            schema.get_table(b"sqlite_Schema").unwrap().root_page_id,
            ROOT_PAGE_ID
        );
    }

    #[test]
    fn get_table_not_found() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE TABLE example2(col1, col2);",
            "CREATE TABLE example3(col1, col2, col3);",
        ]);
        let schema = generate_schema(file.path());

        assert!(schema.get_table(b"invalid").is_none());
    }

    #[test]
    fn parse_table() {
        let (table_name, table) = Table::parse(
            b"create table example(col, col1 integer primary key, \"col2\" text, `co``l3` blob, [col4] real, col5 other)",
            1,
        )
        .unwrap();
        assert_eq!(table_name, b"example");
        assert_eq!(
            table,
            Table {
                root_page_id: 1,
                columns: vec![
                    Column {
                        name: b"col".to_vec(),
                        type_affinity: TypeAffinity::Blob,
                        primary_key: false,
                        collation: Collation::Binary,
                    },
                    Column {
                        name: b"col1".to_vec(),
                        type_affinity: TypeAffinity::Integer,
                        primary_key: true,
                        collation: Collation::Binary,
                    },
                    Column {
                        name: b"col2".to_vec(),
                        type_affinity: TypeAffinity::Text,
                        primary_key: false,
                        collation: Collation::Binary,
                    },
                    Column {
                        name: b"co`l3".to_vec(),
                        type_affinity: TypeAffinity::Blob,
                        primary_key: false,
                        collation: Collation::Binary,
                    },
                    Column {
                        name: b"col4".to_vec(),
                        type_affinity: TypeAffinity::Real,
                        primary_key: false,
                        collation: Collation::Binary,
                    },
                    Column {
                        name: b"col5".to_vec(),
                        type_affinity: TypeAffinity::Numeric,
                        primary_key: false,
                        collation: Collation::Binary,
                    },
                ],
                indexes: None,
            }
        );

        // multiple primary key
        assert!(Table::parse(
            b"create table example(col, col1 integer primary key, col2 text primary key)",
            1
        )
        .is_err());
        // duplicated column name
        assert!(Table::parse(b"create table example(col, cOl integer)", 2).is_err());
    }

    #[test]
    fn test_parse_table_collation() {
        let (_, table) = Table::parse(
            b"create table example(col, col1 collate binary primary key, col2 collate nocase, col3 text collate rtrim, col4 collate binary collate nocase collate rtrim)",
            1,
        )
        .unwrap();

        assert_eq!(table.columns[0].collation, Collation::Binary);
        assert_eq!(table.columns[1].collation, Collation::Binary);
        assert_eq!(table.columns[2].collation, Collation::NoCase);
        assert_eq!(table.columns[3].collation, Collation::RTrim);
        assert_eq!(table.columns[4].collation, Collation::RTrim);

        let (_, table) = Table::parse(
            b"create table example(col1 collate BINARY primary key, col2 collate NOCASE, col3 text collate RTRIM, col4 collate NoCase, col5 collate \"NoCase\")",
            1,
        )
        .unwrap();

        assert_eq!(table.columns[0].collation, Collation::Binary);
        assert_eq!(table.columns[1].collation, Collation::NoCase);
        assert_eq!(table.columns[2].collation, Collation::RTrim);
        assert_eq!(table.columns[3].collation, Collation::NoCase);
        assert_eq!(table.columns[4].collation, Collation::NoCase);

        // unknown collation
        assert!(Table::parse(
            b"create table example(col collate invalid collate binary)",
            1,
        )
        .is_err());
    }

    #[test]
    fn get_table() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE TABLE \"example2\"(col1 null, col2 integer);",
            "CREATE TABLE `exam``ple3`(COL1 real, Col2 text primary key, cOL3 blob, _);",
            "CREATE TABLE [example4](id integer primary key, col);",
            "create table example5(col, col1 integer primary key collate binary, \"col2\" text collate nocase, `co``l3` blob collate rtrim, [col4] real, col5 other)",
        ]);
        let schema = generate_schema(file.path());

        assert_eq!(
            schema.get_table(b"example").unwrap(),
            &Table {
                root_page_id: 2,
                columns: vec![Column {
                    name: b"col".to_vec(),
                    type_affinity: TypeAffinity::Blob,
                    primary_key: false,
                    collation: Collation::Binary,
                }],
                indexes: None,
            }
        );
        assert_eq!(
            schema.get_table(b"example2").unwrap().columns,
            vec![
                Column {
                    name: b"col1".to_vec(),
                    type_affinity: TypeAffinity::Numeric,
                    primary_key: false,
                    collation: Collation::Binary,
                },
                Column {
                    name: b"col2".to_vec(),
                    type_affinity: TypeAffinity::Integer,
                    primary_key: false,
                    collation: Collation::Binary,
                }
            ]
        );
        assert_eq!(
            schema.get_table(b"exam`ple3").unwrap().columns,
            vec![
                Column {
                    name: b"COL1".to_vec(),
                    type_affinity: TypeAffinity::Real,
                    primary_key: false,
                    collation: Collation::Binary,
                },
                Column {
                    name: b"Col2".to_vec(),
                    type_affinity: TypeAffinity::Text,
                    primary_key: true,
                    collation: Collation::Binary,
                },
                Column {
                    name: b"cOL3".to_vec(),
                    type_affinity: TypeAffinity::Blob,
                    primary_key: false,
                    collation: Collation::Binary,
                },
                Column {
                    name: b"_".to_vec(),
                    type_affinity: TypeAffinity::Blob,
                    primary_key: false,
                    collation: Collation::Binary,
                }
            ]
        );
        assert!(schema.get_table(b"example4").is_some());
        assert_eq!(
            schema.get_table(b"example5").unwrap().columns,
            vec![
                Column {
                    name: b"col".to_vec(),
                    type_affinity: TypeAffinity::Blob,
                    primary_key: false,
                    collation: Collation::Binary,
                },
                Column {
                    name: b"col1".to_vec(),
                    type_affinity: TypeAffinity::Integer,
                    primary_key: true,
                    collation: Collation::Binary,
                },
                Column {
                    name: b"col2".to_vec(),
                    type_affinity: TypeAffinity::Text,
                    primary_key: false,
                    collation: Collation::NoCase,
                },
                Column {
                    name: b"co`l3".to_vec(),
                    type_affinity: TypeAffinity::Blob,
                    primary_key: false,
                    collation: Collation::RTrim,
                },
                Column {
                    name: b"col4".to_vec(),
                    type_affinity: TypeAffinity::Real,
                    primary_key: false,
                    collation: Collation::Binary,
                },
                Column {
                    name: b"col5".to_vec(),
                    type_affinity: TypeAffinity::Numeric,
                    primary_key: false,
                    collation: Collation::Binary,
                },
            ]
        );
    }

    #[test]
    fn test_get_table_type_affinity() {
        let file = create_sqlite_database(&[
            "CREATE TABLE integer(col1 long real blob text `Int``eger`, col2 integer text, col3 varint, col4 FLOAT POINT);",
            "CREATE TABLE text(col1 long real blob chAr, col2 long cLoB blob, col3 longteXt);",
            "CREATE TABLE blob(col1 long real Blob, col2, col3 bblob);",
            "CREATE TABLE real(col1 long Real, col2 float, col3 dOuble);",
            "CREATE TABLE numeric(col1 null, col2 long long, col3 `in``teger`);",
        ]);
        let schema = generate_schema(file.path());

        let table = schema.get_table(b"integer").unwrap();
        assert_eq!(table.columns.len(), 4);
        for column in &table.columns {
            assert_eq!(
                column.type_affinity,
                TypeAffinity::Integer,
                "column: {:?}",
                column
            );
        }

        let table = schema.get_table(b"text").unwrap();
        assert_eq!(table.columns.len(), 3);
        for column in &table.columns {
            assert_eq!(
                column.type_affinity,
                TypeAffinity::Text,
                "column: {:?}",
                column
            );
        }

        let table = schema.get_table(b"blob").unwrap();
        assert_eq!(table.columns.len(), 3);
        for column in &table.columns {
            assert_eq!(
                column.type_affinity,
                TypeAffinity::Blob,
                "column: {:?}",
                column
            );
        }

        let table = schema.get_table(b"real").unwrap();
        assert_eq!(table.columns.len(), 3);
        for column in &table.columns {
            assert_eq!(
                column.type_affinity,
                TypeAffinity::Real,
                "column: {:?}",
                column
            );
        }

        let table = schema.get_table(b"numeric").unwrap();
        assert_eq!(table.columns.len(), 3);
        for column in &table.columns {
            assert_eq!(
                column.type_affinity,
                TypeAffinity::Numeric,
                "column: {:?}",
                column
            );
        }
    }

    #[test]
    fn test_table_get_column_index() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE TABLE example2(col1 integer, col2, rowid);",
            "CREATE TABLE example3(id integer primary key, col);",
            "CREATE TABLE example4(id text primary key, col);",
        ]);
        let schema = generate_schema(file.path());

        let table = schema.get_table(b"example").unwrap();
        assert_eq!(table.get_column(b"col").unwrap().0, ColumnNumber::Column(0));
        assert_eq!(table.get_column(b"rowid").unwrap().0, ColumnNumber::RowId);
        assert!(table.get_column(b"invalid").is_none());

        let table = schema.get_table(b"example2").unwrap();
        assert_eq!(
            table.get_column(b"col1").unwrap().0,
            ColumnNumber::Column(0)
        );
        assert_eq!(
            table.get_column(b"col2").unwrap().0,
            ColumnNumber::Column(1)
        );
        assert_eq!(
            table.get_column(b"rowid").unwrap().0,
            ColumnNumber::Column(2)
        );
        assert!(table.get_column(b"invalid").is_none());

        let table = schema.get_table(b"example3").unwrap();
        assert_eq!(table.get_column(b"id").unwrap().0, ColumnNumber::RowId);
        assert_eq!(table.get_column(b"col").unwrap().0, ColumnNumber::Column(1));
        assert_eq!(table.get_column(b"rowid").unwrap().0, ColumnNumber::RowId);

        let table = schema.get_table(b"example4").unwrap();
        assert_eq!(table.get_column(b"id").unwrap().0, ColumnNumber::Column(0));
        assert_eq!(table.get_column(b"col").unwrap().0, ColumnNumber::Column(1));
        assert_eq!(table.get_column(b"rowid").unwrap().0, ColumnNumber::RowId);
    }

    #[test]
    fn test_table_get_all_columns() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE TABLE example2(col1, col2, rowid);",
            "CREATE TABLE example3(col1, id integer primary key, col2 collate nocase);",
            "CREATE TABLE example4(col1, id text primary key collate rtrim, col2);",
        ]);
        let schema = generate_schema(file.path());

        let table = schema.get_table(b"example").unwrap();
        let mut iter = table.get_all_columns();
        assert_eq!(
            iter.next(),
            Some((
                ColumnNumber::Column(0),
                TypeAffinity::Blob,
                Collation::Binary
            ))
        );
        assert_eq!(iter.next(), None);

        let table = schema.get_table(b"example2").unwrap();
        let mut iter = table.get_all_columns();
        assert_eq!(
            iter.next(),
            Some((
                ColumnNumber::Column(0),
                TypeAffinity::Blob,
                Collation::Binary
            ))
        );
        assert_eq!(
            iter.next(),
            Some((
                ColumnNumber::Column(1),
                TypeAffinity::Blob,
                Collation::Binary
            ))
        );
        assert_eq!(
            iter.next(),
            Some((
                ColumnNumber::Column(2),
                TypeAffinity::Blob,
                Collation::Binary
            ))
        );
        assert_eq!(iter.next(), None);

        let table = schema.get_table(b"example3").unwrap();
        let mut iter = table.get_all_columns();
        assert_eq!(
            iter.next(),
            Some((
                ColumnNumber::Column(0),
                TypeAffinity::Blob,
                Collation::Binary
            ))
        );
        assert_eq!(
            iter.next(),
            Some((
                ColumnNumber::RowId,
                TypeAffinity::Integer,
                Collation::Binary
            ))
        );
        assert_eq!(
            iter.next(),
            Some((
                ColumnNumber::Column(2),
                TypeAffinity::Blob,
                Collation::NoCase
            ))
        );
        assert_eq!(iter.next(), None);

        let table = schema.get_table(b"example4").unwrap();
        let mut iter = table.get_all_columns();
        assert_eq!(
            iter.next(),
            Some((
                ColumnNumber::Column(0),
                TypeAffinity::Blob,
                Collation::Binary
            ))
        );
        assert_eq!(
            iter.next(),
            Some((
                ColumnNumber::Column(1),
                TypeAffinity::Text,
                Collation::RTrim
            ))
        );
        assert_eq!(
            iter.next(),
            Some((
                ColumnNumber::Column(2),
                TypeAffinity::Blob,
                Collation::Binary
            ))
        );
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn get_index_success() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col1, col2);",
            "CREATE INDEX index1 ON example(col1);",
            "CREATE INDEX index2 ON example(col1, col2);",
        ]);
        let schema = generate_schema(file.path());

        let index1 = Rc::new(Index {
            root_page_id: 3,
            columns: vec![ColumnNumber::Column(0)],
            next: None,
        });
        let index2 = Rc::new(Index {
            root_page_id: 4,
            columns: vec![ColumnNumber::Column(0), ColumnNumber::Column(1)],
            next: Some(index1.clone()),
        });
        assert_eq!(schema.get_index(b"index1").unwrap(), &index1);
        assert_eq!(schema.get_index(b"index2").unwrap(), &index2);
    }

    #[test]
    fn get_index_success_quoted_table_name() {
        let file = create_sqlite_database(&[
            "CREATE TABLE `exam``ple`(col1, col2);",
            "CREATE INDEX index1 ON \"exam`ple\"(col1);",
            "CREATE INDEX index2 ON `exam``ple`(col1, col2);",
        ]);
        let schema = generate_schema(file.path());

        let index1 = Rc::new(Index {
            root_page_id: 3,
            columns: vec![ColumnNumber::Column(0)],
            next: None,
        });
        let index2 = Rc::new(Index {
            root_page_id: 4,
            columns: vec![ColumnNumber::Column(0), ColumnNumber::Column(1)],
            next: Some(index1.clone()),
        });
        assert_eq!(schema.get_index(b"index1").unwrap(), &index1);
        assert_eq!(schema.get_index(b"index2").unwrap(), &index2);
    }

    #[test]
    fn get_table_with_index() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col1, col2);",
            "CREATE INDEX index1 ON example(col1);",
            "CREATE INDEX index2 ON example(col1, col2);",
        ]);
        let schema = generate_schema(file.path());

        let table = schema.get_table(b"example").unwrap();

        let index1 = Rc::new(Index {
            root_page_id: 3,
            columns: vec![ColumnNumber::Column(0)],
            next: None,
        });
        let index2 = Rc::new(Index {
            root_page_id: 4,
            columns: vec![ColumnNumber::Column(0), ColumnNumber::Column(1)],
            next: Some(index1.clone()),
        });
        assert_eq!(table.indexes, Some(index2));
    }

    #[test]
    fn get_index_case_insensitive() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col1, col2);",
            "CREATE INDEX inDex1 ON example(col1);",
            "CREATE INDEX index2 ON example(col1, col2);",
        ]);
        let schema = generate_schema(file.path());

        assert_eq!(schema.get_index(b"index1").unwrap().root_page_id, 3);
        assert_eq!(schema.get_index(b"inDex2").unwrap().root_page_id, 4);
    }

    #[test]
    fn get_index_not_found() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col1, col2);",
            "CREATE INDEX index1 ON example(col1);",
            "CREATE INDEX index2 ON example(col1, col2);",
        ]);
        let schema = generate_schema(file.path());

        assert!(schema.get_index(b"invalid").is_none());
    }

    #[test]
    fn parse_index() {
        let (_, table) = Table::parse(
            b"create table example(col1, id integer primary key, col2)",
            1,
        )
        .unwrap();
        let (index_name, table_name, index) =
            Index::parse(b"create index index1 on example(id, col1, col2)", 3, &table).unwrap();
        assert_eq!(index_name, b"index1");
        assert_eq!(table_name, b"example".as_slice().into());
        assert_eq!(
            index,
            Index {
                root_page_id: 3,
                columns: vec![
                    ColumnNumber::RowId,
                    ColumnNumber::Column(0),
                    ColumnNumber::Column(2)
                ],
                next: None,
            }
        );
        // unknown column
        assert!(Index::parse(b"create index index1 on example(col1, invalid)", 3, &table).is_err());
        // unknown table
        let (_, table_name, _) =
            Index::parse(b"create index index1 on invalid(col1)", 3, &table).unwrap();
        assert_eq!(table_name, b"invalid".as_slice().into());
    }
}
