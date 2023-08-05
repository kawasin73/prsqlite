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
use std::collections::HashSet;
use std::iter::Iterator;
use std::rc::Rc;

use anyhow::bail;
use anyhow::Context;

pub use crate::btree::*;
use crate::pager::PageId;
use crate::pager::ROOT_PAGE_ID;
use crate::parser::parse_create_index;
use crate::parser::parse_create_table;
pub use crate::parser::DataType;
use crate::record::Value;
use crate::utils::upper_to_lower;
use crate::utils::CaseInsensitiveBytes;
use crate::Columns;
use crate::Statement;

struct SchemaRecord<'a> {
    type_: &'a str,
    name: &'a str,
    table_name: &'a str,
    root_page_id: u32,
    sql: Option<&'a str>,
}

impl<'a> SchemaRecord<'a> {
    fn parse(columns: Columns<'a>) -> anyhow::Result<Self> {
        let &Value::Text(type_) = columns.get(0) else {
            bail!("invalid type: {:?}", columns.get(0));
        };

        let &Value::Text(name) = columns.get(1) else {
            bail!("invalid name: {:?}", columns.get(1));
        };

        let &Value::Text(table_name) = columns.get(2) else {
            bail!("invalid tbl_name: {:?}", columns.get(2));
        };

        let &Value::Integer(root_page_id) = columns.get(3) else {
            bail!("invalid root_page_id: {:?}", columns.get(3));
        };
        let root_page_id = root_page_id.try_into().context("parse root_page_id")?;

        let sql = match *columns.get(4) {
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
                    data_type: Some(DataType::Text),
                    primary_key: false,
                },
                Column {
                    name: b"name".to_vec(),
                    data_type: Some(DataType::Text),
                    primary_key: false,
                },
                Column {
                    name: b"tbl_name".to_vec(),
                    data_type: Some(DataType::Text),
                    primary_key: false,
                },
                Column {
                    name: b"rootpage".to_vec(),
                    data_type: Some(DataType::Integer),
                    primary_key: false,
                },
                Column {
                    name: b"sql".to_vec(),
                    data_type: Some(DataType::Text),
                    primary_key: false,
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
            let schema = SchemaRecord::parse(columns)?;
            match schema.type_ {
                "table" => {
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
                    if table_name != schema.name.as_bytes() {
                        bail!(
                            "table name does not match: table_name={:?}, parsed_table_name={:?}",
                            schema.table_name,
                            table_name
                        );
                    }
                    upper_to_lower(&mut table_name);
                    tables.insert(table_name, table);
                }
                "index" => {
                    // schema.table_name is already lowercased in the file generated by sqlite3.
                    // However pessimisticly lowercased here.
                    let table = tables
                        .get_mut(schema.table_name.to_lowercase().as_bytes())
                        .context("index table not found")?;
                    if let Some(sql) = schema.sql {
                        let (mut index_name, table_name, mut index) =
                            Index::parse(sql, schema.root_page_id, table)?;
                        if index_name != schema.name.as_bytes() {
                            bail!(
                                "index name does not match: index_name={:?}, parsed_index_name={:?}",
                                schema.name,
                                index_name
                            );
                        } else if CaseInsensitiveBytes::from(table_name)
                            != CaseInsensitiveBytes::from(schema.table_name.as_bytes())
                        {
                            bail!(
                                "index table name does not match: table_name={:?}, parsed_table_name={:?}",
                                schema.table_name,
                                table_name
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
                "view" => {
                    // TODO: support view
                }
                "trigger" => {
                    // TODO: support trigger
                }
                type_ => {
                    bail!("unsupported type: {:?}", type_);
                }
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
        sql: &'a str,
        root_page_id: PageId,
        table: &Table,
    ) -> anyhow::Result<(Vec<u8>, &'a [u8], Self)> {
        let (n, create_index) = parse_create_index(sql.as_bytes())
            .map_err(|e| anyhow::anyhow!("parse create index sql: {:?}", e))?;
        if n != sql.as_bytes().len() {
            bail!(
                "create table sql in sqlite_schema contains useless contents at the tail: {}",
                sql
            );
        }
        let mut columns = Vec::with_capacity(create_index.columns.len());
        for column in &create_index.columns {
            let Some(column_number) = table.get_column_index(column.name) else {
                bail!(
                    "column {:?} in create index sql is not found in table {:?}",
                    column.name,
                    table
                );
            };
            columns.push(column_number);
        }
        Ok((
            create_index.index_name.to_vec(),
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
    pub data_type: Option<DataType>,
    pub primary_key: bool,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ColumnNumber {
    RowId,
    Column(usize),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Table {
    pub root_page_id: PageId,
    pub columns: Vec<Column>,
    pub indexes: Option<Rc<Index>>,
}

impl Table {
    fn parse(sql: &str, root_page_id: PageId) -> anyhow::Result<(Vec<u8>, Self)> {
        let (n, create_table) = parse_create_table(sql.as_bytes())
            .map_err(|e| anyhow::anyhow!("parse create table sql: {:?}", e))?;
        if n != sql.as_bytes().len() {
            bail!(
                "create table sql in sqlite_schema contains useless contents at the tail: {}",
                sql
            );
        }
        let name = create_table.table_name.to_vec();
        let mut columns = Vec::with_capacity(create_table.columns.len());
        let mut has_primary_key = false;
        let mut column_name_set = HashSet::new();
        for column_def in create_table.columns {
            if column_def.primary_key {
                if has_primary_key {
                    bail!("multiple primary key");
                }
                has_primary_key = true;
            }
            let column_name = CaseInsensitiveBytes::from(column_def.name);
            if column_name_set.contains(&column_name) {
                bail!("duplicate column name: {:?}", column_def.name);
            }
            column_name_set.insert(column_name);

            columns.push(Column {
                name: column_def.name.to_vec(),
                data_type: column_def.data_type,
                primary_key: column_def.primary_key,
            });
        }
        Ok((
            name,
            Table {
                root_page_id,
                columns,
                indexes: None,
            },
        ))
    }

    pub fn get_column_index(&self, column: &[u8]) -> Option<ColumnNumber> {
        let column = CaseInsensitiveBytes::from(column);
        if let Some(i) = self
            .columns
            .iter()
            .position(|c| CaseInsensitiveBytes::from(&c.name) == column)
        {
            let column = &self.columns[i];
            if column.primary_key && column.data_type == Some(DataType::Integer) {
                Some(ColumnNumber::RowId)
            } else {
                Some(ColumnNumber::Column(i))
            }
        } else if column.equal_to_lower_bytes(&b"rowid"[..]) {
            Some(ColumnNumber::RowId)
        } else {
            None
        }
    }

    pub fn all_column_index(&self) -> impl Iterator<Item = ColumnNumber> + '_ {
        self.columns.iter().enumerate().map(|(i, column)| {
            if column.primary_key && column.data_type == Some(DataType::Integer) {
                ColumnNumber::RowId
            } else {
                ColumnNumber::Column(i)
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

    fn generate_schema(filepath: &Path) -> Schema {
        let mut conn = Connection::open(filepath).unwrap();
        let schema_table = Schema::schema_table();
        let columns = schema_table.all_column_index().collect::<Vec<_>>();
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
        let (table_name, table) =
            Table::parse("create table example(col, col1 integer primary key)", 1).unwrap();
        assert_eq!(table_name, b"example");
        assert_eq!(
            table,
            Table {
                root_page_id: 1,
                columns: vec![
                    Column {
                        name: b"col".to_vec(),
                        data_type: None,
                        primary_key: false,
                    },
                    Column {
                        name: b"col1".to_vec(),
                        data_type: Some(DataType::Integer),
                        primary_key: true,
                    },
                ],
                indexes: None,
            }
        );
        // multiple primary key
        assert!(Table::parse(
            "create table example(col, col1 integer primary key, col2 text primary key)",
            1
        )
        .is_err());
        // duplicated column name
        assert!(Table::parse("create table example(col, col integer)", 2).is_err());
    }

    #[test]
    fn get_table() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE TABLE example2(col1 null, col2 integer);",
            "CREATE TABLE example3(COL1 real, Col2 text primary key, cOL3 blob, _);",
            "CREATE TABLE example4(id integer primary key, col);",
        ]);
        let schema = generate_schema(file.path());

        assert_eq!(
            schema.get_table(b"example").unwrap(),
            &Table {
                root_page_id: 2,
                columns: vec![Column {
                    name: b"col".to_vec(),
                    data_type: None,
                    primary_key: false,
                }],
                indexes: None,
            }
        );
        assert_eq!(
            schema.get_table(b"example2").unwrap().columns,
            vec![
                Column {
                    name: b"col1".to_vec(),
                    data_type: Some(DataType::Null),
                    primary_key: false,
                },
                Column {
                    name: b"col2".to_vec(),
                    data_type: Some(DataType::Integer),
                    primary_key: false,
                }
            ]
        );
        assert_eq!(
            schema.get_table(b"example3").unwrap().columns,
            vec![
                Column {
                    name: b"COL1".to_vec(),
                    data_type: Some(DataType::Real),
                    primary_key: false,
                },
                Column {
                    name: b"Col2".to_vec(),
                    data_type: Some(DataType::Text),
                    primary_key: true,
                },
                Column {
                    name: b"cOL3".to_vec(),
                    data_type: Some(DataType::Blob),
                    primary_key: false,
                },
                Column {
                    name: b"_".to_vec(),
                    data_type: None,
                    primary_key: false,
                }
            ]
        );
        assert_eq!(
            schema.get_table(b"example4").unwrap().columns,
            vec![
                Column {
                    name: b"id".to_vec(),
                    data_type: Some(DataType::Integer),
                    primary_key: true,
                },
                Column {
                    name: b"col".to_vec(),
                    data_type: None,
                    primary_key: false,
                }
            ]
        );
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
        assert_eq!(
            table.get_column_index(b"col"),
            Some(ColumnNumber::Column(0))
        );
        assert_eq!(table.get_column_index(b"rowid"), Some(ColumnNumber::RowId));
        assert_eq!(table.get_column_index(b"invalid"), None);

        let table = schema.get_table(b"example2").unwrap();
        assert_eq!(
            table.get_column_index(b"col1"),
            Some(ColumnNumber::Column(0))
        );
        assert_eq!(
            table.get_column_index(b"col2"),
            Some(ColumnNumber::Column(1))
        );
        assert_eq!(
            table.get_column_index(b"rowid"),
            Some(ColumnNumber::Column(2))
        );
        assert_eq!(table.get_column_index(b"invalid"), None);

        let table = schema.get_table(b"example3").unwrap();
        assert_eq!(table.get_column_index(b"id"), Some(ColumnNumber::RowId));
        assert_eq!(
            table.get_column_index(b"col"),
            Some(ColumnNumber::Column(1))
        );
        assert_eq!(table.get_column_index(b"rowid"), Some(ColumnNumber::RowId));

        let table = schema.get_table(b"example4").unwrap();
        assert_eq!(table.get_column_index(b"id"), Some(ColumnNumber::Column(0)));
        assert_eq!(
            table.get_column_index(b"col"),
            Some(ColumnNumber::Column(1))
        );
        assert_eq!(table.get_column_index(b"rowid"), Some(ColumnNumber::RowId));
    }

    #[test]
    fn test_table_all_column_index() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE TABLE example2(col1, col2, rowid);",
            "CREATE TABLE example3(col1, id integer primary key, col2);",
            "CREATE TABLE example4(col1, id text primary key, col2);",
        ]);
        let schema = generate_schema(file.path());

        let table = schema.get_table(b"example").unwrap();
        let mut iter = table.all_column_index();
        assert_eq!(iter.next(), Some(ColumnNumber::Column(0)));
        assert_eq!(iter.next(), None);

        let table = schema.get_table(b"example2").unwrap();
        let mut iter = table.all_column_index();
        assert_eq!(iter.next(), Some(ColumnNumber::Column(0)));
        assert_eq!(iter.next(), Some(ColumnNumber::Column(1)));
        assert_eq!(iter.next(), Some(ColumnNumber::Column(2)));
        assert_eq!(iter.next(), None);

        let table = schema.get_table(b"example3").unwrap();
        let mut iter = table.all_column_index();
        assert_eq!(iter.next(), Some(ColumnNumber::Column(0)));
        assert_eq!(iter.next(), Some(ColumnNumber::RowId));
        assert_eq!(iter.next(), Some(ColumnNumber::Column(2)));
        assert_eq!(iter.next(), None);

        let table = schema.get_table(b"example4").unwrap();
        let mut iter = table.all_column_index();
        assert_eq!(iter.next(), Some(ColumnNumber::Column(0)));
        assert_eq!(iter.next(), Some(ColumnNumber::Column(1)));
        assert_eq!(iter.next(), Some(ColumnNumber::Column(2)));
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
            "create table example(col1, id integer primary key, col2)",
            1,
        )
        .unwrap();
        let (index_name, table_name, index) =
            Index::parse("create index index1 on example(id, col1, col2)", 3, &table).unwrap();
        assert_eq!(index_name, b"index1");
        assert_eq!(table_name, b"example");
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
        assert!(Index::parse("create index index1 on example(col1, invalid)", 3, &table).is_err());
        // unknown table
        let (_, table_name, _) =
            Index::parse("create index index1 on invalid(col1)", 3, &table).unwrap();
        assert_eq!(table_name, b"invalid");
    }
}
