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

use anyhow::bail;
use anyhow::Context;

pub use crate::btree::*;
use crate::pager::PageId;
use crate::pager::ROOT_PAGE_ID;
use crate::parser::parse_create_table;
use crate::record::Value;
use crate::utils::upper_to_lower;
use crate::Columns;
use crate::Statement;

struct SchemaRecord<'a> {
    type_: &'a str,
    name: &'a str,
    table_name: &'a str,
    root_page_id: u32,
    sql: &'a str,
}

impl<'a> SchemaRecord<'a> {
    fn parse(columns: Columns<'a>) -> anyhow::Result<Self> {
        let type_ = if let &Value::Text(type_) = columns.get(0) {
            type_
        } else {
            bail!("invalid type");
        };
        let name = if let &Value::Text(name) = columns.get(1) {
            name
        } else {
            bail!("invalid name");
        };
        let table_name = if let &Value::Text(table_name) = columns.get(2) {
            table_name
        } else {
            bail!("invalid table name");
        };
        let root_page_id = if let &Value::Integer(root_page_id) = columns.get(3) {
            root_page_id.try_into().context("parse root_page_id")?
        } else {
            bail!("invalid table name");
        };
        let sql = if let &Value::Text(sql) = columns.get(4) {
            sql
        } else {
            bail!("invalid table name");
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
}

impl Schema {
    pub fn schema_table() -> Table {
        Table {
            root_page_id: ROOT_PAGE_ID,
            columns: vec![
                b"type".to_vec(),
                b"name".to_vec(),
                b"tbl_name".to_vec(),
                b"rootpage".to_vec(),
                b"sql".to_vec(),
            ],
        }
    }

    pub fn generate(stmt: Statement, schema_table: Table) -> anyhow::Result<Schema> {
        let mut stmt = stmt;
        let mut rows = stmt.execute()?;
        let mut tables = HashMap::new();
        while let Some(mut row) = rows.next()? {
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
                    let (n, create_table) = parse_create_table(schema.sql.as_bytes())
                        .map_err(|e| anyhow::anyhow!("parse create table sql: {:?}", e))?;
                    if create_table.table_name != schema.name.as_bytes() {
                        bail!(
                            "table name does not match: table_name={:?}, parsed_table_name={:?}",
                            schema.table_name,
                            create_table.table_name
                        );
                    }
                    if n != schema.sql.as_bytes().len() {
                        bail!(
                            "create table sql in sqlite_schema contains useless contents at the tail: {}",
                            schema.sql
                        );
                    }
                    let columns = create_table.columns.iter().map(|name| name.to_vec()).collect();
                    let table = Table {
                        root_page_id: schema.root_page_id,
                        columns,
                    };
                    let mut key = schema.name.as_bytes().to_vec();
                    upper_to_lower(&mut key);
                    tables.insert(key, table);
                }
                "index" => {
                    // TODO: support index
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
        Ok(Self { schema_table, tables })
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
}

pub struct Table {
    pub root_page_id: PageId,
    pub columns: Vec<Vec<u8>>,
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
        let columns = (0..schema_table.columns.len()).collect::<Vec<_>>();
        Schema::generate(
            Statement::new(&mut conn, schema_table.root_page_id, columns),
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
        let file = create_sqlite_database(&queries.iter().map(|q| q.as_str()).collect::<Vec<&str>>());
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

        assert_eq!(schema.get_table(b"sqlite_schema").unwrap().root_page_id, ROOT_PAGE_ID);
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
        assert_eq!(schema.get_table(b"sqlite_Schema").unwrap().root_page_id, ROOT_PAGE_ID);
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
    fn get_table_columns() {
        let file = create_sqlite_database(&[
            "CREATE TABLE example(col);",
            "CREATE TABLE example2(col1, col2);",
            "CREATE TABLE example3(COL1, COL2, COL3, _);",
        ]);
        let schema = generate_schema(file.path());

        assert_eq!(schema.get_table(b"example").unwrap().columns, vec![b"col".to_vec()]);
        assert_eq!(
            schema.get_table(b"example2").unwrap().columns,
            vec![b"col1".to_vec(), b"col2".to_vec()]
        );
        assert_eq!(
            schema.get_table(b"example3").unwrap().columns,
            vec![b"COL1".to_vec(), b"COL2".to_vec(), b"COL3".to_vec(), b"_".to_vec()]
        );
    }
}
