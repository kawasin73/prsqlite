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

use std::fmt::Display;

use crate::token::get_token;
use crate::token::Token;
use crate::utils::parse_float;
use crate::utils::parse_integer;
use crate::utils::HexedBytes;
use crate::utils::MaybeQuotedBytes;
use crate::utils::ParseIntegerResult;

#[derive(Debug)]
pub struct Error<'a> {
    input: &'a [u8],
    cursor: usize,
    token_size: usize,
    msg: &'static str,
}

impl Error<'_> {
    /// This is for testing.
    #[allow(dead_code)]
    pub fn cursor(&self) -> usize {
        self.cursor
    }
}

impl Display for Error<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Ok(sql) = std::str::from_utf8(self.input) else {
            return Err(std::fmt::Error);
        };
        // TODO: Adjust character width
        let mut n_chars = 0;
        let mut rest_bytes = self.cursor;
        for c in sql.chars() {
            if c.len_utf8() > rest_bytes {
                break;
            }
            rest_bytes -= c.len_utf8();
            n_chars += 1;
        }
        let token_size = if self.token_size > 0 {
            self.token_size
        } else {
            1
        };
        write!(
            f,
            "{}\n{}\n{}{}",
            self.msg,
            sql,
            " ".repeat(n_chars),
            "^".repeat(token_size)
        )
    }
}

pub type Result<'a, T> = std::result::Result<T, Error<'a>>;

static NULL_BYTES: &[u8] = b"null";

#[derive(Debug, Clone)]
pub struct Parser<'a> {
    input: &'a [u8],
    cursor: usize,
    token: Option<Token<'a>>,
    token_size: usize,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a [u8]) -> Self {
        let mut parser = Self {
            input,
            cursor: 0,
            token: None,
            token_size: 0,
        };
        parser.next();
        parser
    }

    /// Return the number of bytes consumed by the parser.
    ///
    /// This is used for testing.
    #[allow(dead_code)]
    pub fn n_consumed(&self) -> usize {
        self.cursor
    }

    fn next<'b>(&'b mut self) -> Option<&'b Token<'a>> {
        self.cursor += self.token_size;
        if let Some((n, token)) = get_token(&self.input[self.cursor..]) {
            self.token_size = n;
            if token == Token::Space {
                return self.next();
            }
            self.token = Some(token);
            self.token.as_ref()
        } else {
            self.token_size = 0;
            self.token = None;
            None
        }
    }

    fn peek<'b>(&'b self) -> Option<&'b Token<'a>> {
        self.token.as_ref()
    }

    fn error(&self, msg: &'static str) -> Error<'a> {
        Error {
            input: self.input,
            cursor: self.cursor,
            token_size: self.token_size,
            msg,
        }
    }
}

pub enum Stmt<'a> {
    Select(Select<'a>),
    Insert(Insert<'a>),
}

pub fn parse_sql<'a>(p: &mut Parser<'a>) -> Result<'a, Stmt<'a>> {
    match p.peek() {
        Some(Token::Select) => {
            let select = parse_select(p)?;
            Ok(Stmt::Select(select))
        }
        Some(Token::Insert) => {
            let select = parse_insert(p)?;
            Ok(Stmt::Insert(select))
        }
        _ => Err(p.error("no statement")),
    }
}

/// Assert that the next token is a semicolon.
pub fn expect_semicolon<'a>(p: &mut Parser<'a>) -> Result<'a, ()> {
    match p.peek() {
        Some(Token::Semicolon) => {}
        _ => return Err(p.error("no semicolon")),
    }
    p.next();
    Ok(())
}

/// Assert that there is no token except spaces.
///
/// Uses mutable [Parser] to unify the interface with other expect functions.
pub fn expect_no_more_token<'a>(p: &Parser<'a>) -> Result<'a, ()> {
    match p.peek() {
        Some(_) => Err(p.error("unexpected token")),
        None => Ok(()),
    }
}

/// CREATE TABLE statement.
#[derive(Debug, PartialEq, Eq)]
pub struct CreateTable<'a> {
    pub table_name: MaybeQuotedBytes<'a>,
    pub columns: Vec<ColumnDef<'a>>,
}

/// Constraint of a column in a table.
#[derive(Debug, PartialEq, Eq)]
pub enum ColumnConstraint<'a> {
    Collate(MaybeQuotedBytes<'a>),
    PrinaryKey,
}

/// https://www.sqlite.org/syntax/column-constraint.html
fn parse_column_constraint<'a>(p: &mut Parser<'a>) -> Result<'a, Option<ColumnConstraint<'a>>> {
    match p.peek() {
        Some(Token::Collate) => {
            let Some(Token::Identifier(collation)) = p.next() else {
                return Err(p.error("no collation name"));
            };
            let collation = *collation;
            p.next();
            Ok(Some(ColumnConstraint::Collate(collation)))
        }
        Some(Token::Primary) => {
            let Some(Token::Key) = p.next() else {
                return Err(p.error("no key after primary"));
            };
            p.next();
            Ok(Some(ColumnConstraint::PrinaryKey))
        }
        _ => Ok(None),
    }
}

/// Definition of a column in a table.
#[derive(Debug, PartialEq, Eq)]
pub struct ColumnDef<'a> {
    pub name: MaybeQuotedBytes<'a>,
    pub type_name: Vec<MaybeQuotedBytes<'a>>,
    pub constraints: Vec<ColumnConstraint<'a>>,
}

/// https://www.sqlite.org/syntax/signed-number.html
fn skip_signed_number<'a>(p: &mut Parser<'a>) -> Result<'a, ()> {
    if matches!(p.peek(), Some(Token::Plus) | Some(Token::Minus)) {
        p.next();
    }
    if !matches!(p.peek(), Some(Token::Integer(_)) | Some(Token::Float(_))) {
        return Err(p.error("no signed number"));
    }
    p.next();
    Ok(())
}

/// https://www.sqlite.org/syntax/type-name.html
fn parse_type_name<'a>(p: &mut Parser<'a>) -> Result<'a, Vec<MaybeQuotedBytes<'a>>> {
    // TODO: Parse type_name to type affinity without converting it to the temporary
    // Vec. Use iterator instead.
    let mut type_name = Vec::new();

    match p.peek() {
        Some(Token::Null) => {
            type_name.push(NULL_BYTES.into());
        }
        Some(Token::Identifier(id)) => {
            type_name.push(*id);
        }
        _ => return Ok(Vec::new()),
    };

    loop {
        match p.next() {
            Some(Token::Null) => {
                type_name.push(NULL_BYTES.into());
            }
            Some(Token::Identifier(id)) => {
                type_name.push(*id);
            }
            Some(Token::LeftParen) => {
                p.next();
                // Just check whether signed numbers are valid and move cursor without
                // parsing the number. Signed numbers in a type name has no meanings to type
                // affinity.
                // https://www.sqlite.org/datatype3.html#affinity_name_examples
                // Parse signed numbers.
                skip_signed_number(p)?;
                if p.peek() == Some(&Token::Comma) {
                    p.next();
                    skip_signed_number(p)?;
                }
                if p.peek() != Some(&Token::RightParen) {
                    return Err(p.error("type name: no right paren"));
                }
                p.next();
                break;
            }
            _ => break,
        };
    }

    Ok(type_name)
}

/// Parse CREATE TABLE statement.
///
/// https://www.sqlite.org/lang_createtable.html
pub fn parse_create_table<'a>(p: &mut Parser<'a>) -> Result<'a, CreateTable<'a>> {
    let Some(Token::Create) = p.peek() else {
        return Err(p.error("no create"));
    };

    let Some(Token::Table) = p.next() else {
        return Err(p.error("no table"));
    };

    let Some(Token::Identifier(table_name)) = p.next() else {
        return Err(p.error("no table_name"));
    };
    let table_name = *table_name;

    let Some(Token::LeftParen) = p.next() else {
        return Err(p.error("no left paren"));
    };

    let mut columns = Vec::new();
    loop {
        // Parse ColumnDef.
        let Some(Token::Identifier(name)) = p.next() else {
            return Err(p.error("no column name"));
        };
        let name = *name;
        p.next();

        let type_name = parse_type_name(p)?;

        let mut constraints = Vec::new();
        while let Some(constraint) = parse_column_constraint(p)? {
            constraints.push(constraint);
        }

        columns.push(ColumnDef {
            name,
            type_name,
            constraints,
        });

        // Parser contains a peekable token after parse_column_constraint().
        match p.peek() {
            Some(Token::Comma) => continue,
            Some(Token::RightParen) => break,
            _ => return Err(p.error("no right paren")),
        }
    }
    p.next();

    Ok(CreateTable {
        table_name,
        columns,
    })
}

/// CREATE INDEX statement.
#[derive(Debug, PartialEq, Eq)]
pub struct CreateIndex<'a> {
    pub index_name: MaybeQuotedBytes<'a>,
    pub table_name: MaybeQuotedBytes<'a>,
    pub columns: Vec<IndexedColumn<'a>>,
}

/// Definition of a column in a index.
#[derive(Debug, PartialEq, Eq)]
pub struct IndexedColumn<'a> {
    pub name: MaybeQuotedBytes<'a>,
}

/// Parse CREATE INDEX statement.
///
/// https://www.sqlite.org/lang_createindex.html
pub fn parse_create_index<'a>(p: &mut Parser<'a>) -> Result<'a, CreateIndex<'a>> {
    let Some(Token::Create) = p.peek() else {
        return Err(p.error("no create"));
    };

    let Some(Token::Index) = p.next() else {
        return Err(p.error("no index"));
    };

    let Some(Token::Identifier(index_name)) = p.next() else {
        return Err(p.error("no index_name"));
    };
    let index_name = *index_name;

    let Some(Token::On) = p.next() else {
        return Err(p.error("no on"));
    };

    let Some(Token::Identifier(table_name)) = p.next() else {
        return Err(p.error("no table_name"));
    };
    let table_name = *table_name;

    let Some(Token::LeftParen) = p.next() else {
        return Err(p.error("no left paren"));
    };

    let mut columns = Vec::new();
    loop {
        let Some(Token::Identifier(name)) = p.next() else {
            return Err(p.error("no column name"));
        };
        let name = *name;

        columns.push(IndexedColumn { name });

        match p.next() {
            Some(Token::Comma) => continue,
            Some(Token::RightParen) => break,
            _ => return Err(p.error("no right paren")),
        }
    }
    p.next();

    Ok(CreateIndex {
        index_name,
        table_name,
        columns,
    })
}

#[derive(Debug)]
pub struct Select<'a> {
    pub table_name: MaybeQuotedBytes<'a>,
    pub columns: Vec<ResultColumn<'a>>,
    pub filter: Option<Expr<'a>>,
}

// Parse SELECT statement.
//
// https://www.sqlite.org/lang_select.html
pub fn parse_select<'a>(p: &mut Parser<'a>) -> Result<'a, Select<'a>> {
    let Some(Token::Select) = p.peek() else {
        return Err(p.error("no select"));
    };
    p.next();

    let result_column = parse_result_column(p)?;

    let mut columns = vec![result_column];
    loop {
        match p.peek() {
            Some(Token::Comma) => {
                p.next();
                let result_column = parse_result_column(p)?;
                columns.push(result_column);
            }
            Some(Token::From) => {
                break;
            }
            _ => return Err(p.error("no from")),
        }
    }
    let Some(Token::Identifier(table_name)) = p.next() else {
        return Err(p.error("no table_name"));
    };
    let table_name = *table_name;

    let filter = if let Some(Token::Where) = p.next() {
        p.next();
        let expr = parse_expr(p)?;
        Some(expr)
    } else {
        None
    };

    Ok(Select {
        table_name,
        columns,
        filter,
    })
}

#[derive(Debug, PartialEq)]
pub enum ResultColumn<'a> {
    All,
    AllOfTable(MaybeQuotedBytes<'a>),
    Expr((Expr<'a>, Option<MaybeQuotedBytes<'a>>)),
}

/// Parse result column.
///
/// https://www.sqlite.org/syntax/result-column.html
fn parse_result_column<'a>(p: &mut Parser<'a>) -> Result<'a, ResultColumn<'a>> {
    match p.peek() {
        Some(Token::Identifier(table_name)) => {
            let table_name = *table_name;
            let mut cloned_parser = p.clone();
            if Some(&Token::Dot) == cloned_parser.next()
                && Some(&Token::Asterisk) == cloned_parser.next()
            {
                cloned_parser.next();
                *p = cloned_parser;
                return Ok(ResultColumn::AllOfTable(table_name));
            }
            // Maybe schema_name.table_name.column_name. Fallback to expr
            // parsing.
        }
        Some(Token::Asterisk) => {
            p.next();
            return Ok(ResultColumn::All);
        }
        _ => {}
    }
    let expr = parse_expr(p)?;
    match p.peek() {
        Some(Token::Identifier(alias)) => {
            let alias = *alias;
            p.next();
            Ok(ResultColumn::Expr((expr, Some(alias))))
        }
        Some(Token::As) => {
            let Some(Token::Identifier(alias)) = p.next() else {
                return Err(p.error("no alias"));
            };
            let alias = *alias;
            p.next();
            Ok(ResultColumn::Expr((expr, Some(alias))))
        }
        _ => Ok(ResultColumn::Expr((expr, None))),
    }
}

#[derive(Debug, PartialEq)]
pub struct Insert<'a> {
    pub table_name: MaybeQuotedBytes<'a>,
    pub columns: Vec<MaybeQuotedBytes<'a>>,
    pub values: Vec<Vec<Expr<'a>>>,
}

// Parse INSERT statement.
//
// https://www.sqlite.org/lang_insert.html
pub fn parse_insert<'a>(p: &mut Parser<'a>) -> Result<'a, Insert<'a>> {
    let Some(Token::Insert) = p.peek() else {
        return Err(p.error("no insert"));
    };
    let Some(Token::Into) = p.next() else {
        return Err(p.error("no into"));
    };
    let Some(Token::Identifier(table_name)) = p.next() else {
        return Err(p.error("no table_name"));
    };
    let table_name = *table_name;

    let Some(Token::LeftParen) = p.next() else {
        return Err(p.error("no left paren"));
    };
    let mut columns = Vec::new();

    loop {
        let Some(Token::Identifier(column_name)) = p.next() else {
            return Err(p.error("no column_name"));
        };
        columns.push(*column_name);
        match p.next() {
            Some(Token::Comma) => continue,
            Some(Token::RightParen) => break,
            _ => return Err(p.error("no right paren")),
        }
    }
    let Some(Token::Values) = p.next() else {
        return Err(p.error("no values"));
    };

    let mut values = Vec::new();
    loop {
        let Some(Token::LeftParen) = p.next() else {
            return Err(p.error("no left paren"));
        };
        p.next();
        let expr = parse_expr(p)?;
        let mut column_values = vec![expr];
        loop {
            match p.peek() {
                Some(Token::Comma) => {
                    p.next();
                    let expr = parse_expr(p)?;
                    column_values.push(expr);
                }
                Some(Token::RightParen) => {
                    break;
                }
                _ => return Err(p.error("no right paren")),
            }
        }
        values.push(column_values);
        let Some(Token::Comma) = p.next() else {
            break;
        };
    }

    Ok(Insert {
        table_name,
        columns,
        values,
    })
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum UnaryOp {
    BitNot,
    Minus,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BinaryOp {
    Compare(CompareOp),
    Concat,
    // TODO: BitOr
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum CompareOp {
    /// Equal to
    Eq,
    /// Not equal to
    Ne,
    /// Greater than
    Gt,
    /// Greater than or equal to
    Ge,
    /// Less than
    Lt,
    /// Less than or equal to
    Le,
}

#[derive(Debug, PartialEq)]
pub enum Expr<'a> {
    Column(MaybeQuotedBytes<'a>),
    UnaryOperator {
        operator: UnaryOp,
        expr: Box<Expr<'a>>,
    },
    Collate {
        expr: Box<Expr<'a>>,
        collation_name: MaybeQuotedBytes<'a>,
    },
    BinaryOperator {
        operator: BinaryOp,
        left: Box<Expr<'a>>,
        right: Box<Expr<'a>>,
    },
    Cast {
        expr: Box<Expr<'a>>,
        type_name: Vec<MaybeQuotedBytes<'a>>,
    },
    Null,
    Integer(i64),
    Real(f64),
    Text(MaybeQuotedBytes<'a>),
    Blob(HexedBytes<'a>),
}

/// Parse expression.
///
/// https://www.sqlite.org/syntax/expr.html
fn parse_expr<'a>(p: &mut Parser<'a>) -> Result<'a, Expr<'a>> {
    parse_expr_eq(p)
}

fn parse_expr_eq<'a>(p: &mut Parser<'a>) -> Result<'a, Expr<'a>> {
    let mut expr = parse_expr_compare(p)?;
    loop {
        let operator = match p.peek() {
            Some(Token::Eq) => BinaryOp::Compare(CompareOp::Eq),
            Some(Token::Ne) => BinaryOp::Compare(CompareOp::Ne),
            _ => break,
        };
        p.next();
        let right = parse_expr_compare(p)?;
        expr = Expr::BinaryOperator {
            operator,
            left: Box::new(expr),
            right: Box::new(right),
        };
    }
    Ok(expr)
}

fn parse_expr_compare<'a>(p: &mut Parser<'a>) -> Result<'a, Expr<'a>> {
    let mut expr = parse_expr_concat(p)?;
    loop {
        let operator = match p.peek() {
            Some(Token::Gt) => BinaryOp::Compare(CompareOp::Gt),
            Some(Token::Ge) => BinaryOp::Compare(CompareOp::Ge),
            Some(Token::Lt) => BinaryOp::Compare(CompareOp::Lt),
            Some(Token::Le) => BinaryOp::Compare(CompareOp::Le),
            _ => break,
        };
        p.next();
        let right = parse_expr_concat(p)?;
        expr = Expr::BinaryOperator {
            operator,
            left: Box::new(expr),
            right: Box::new(right),
        };
    }
    Ok(expr)
}

fn parse_expr_concat<'a>(p: &mut Parser<'a>) -> Result<'a, Expr<'a>> {
    let mut expr = parse_expr_collate(p)?;
    // TODO: -> ->> will be added in the future.
    #[allow(clippy::while_let_loop)]
    loop {
        let operator = match p.peek() {
            Some(Token::Concat) => BinaryOp::Concat,
            _ => break,
        };
        p.next();
        let right = parse_expr_collate(p)?;
        expr = Expr::BinaryOperator {
            operator,
            left: Box::new(expr),
            right: Box::new(right),
        };
    }
    Ok(expr)
}

fn parse_expr_collate<'a>(p: &mut Parser<'a>) -> Result<'a, Expr<'a>> {
    let expr = parse_expr_unary(p)?;
    let mut collation = None;
    while let Some(Token::Collate) = p.peek() {
        let Some(Token::Identifier(collation_name)) = p.next() else {
            return Err(p.error("no collation name"));
        };
        collation = Some(*collation_name);
        p.next();
    }
    if let Some(collation_name) = collation {
        Ok(Expr::Collate {
            expr: Box::new(expr),
            collation_name,
        })
    } else {
        Ok(expr)
    }
}

fn parse_expr_unary<'a>(p: &mut Parser<'a>) -> Result<'a, Expr<'a>> {
    match p.peek() {
        Some(Token::Tilda) => {
            p.next();
            let expr = parse_expr_unary(p)?;
            Ok(Expr::UnaryOperator {
                operator: UnaryOp::BitNot,
                expr: Box::new(expr),
            })
        }
        Some(Token::Plus) => {
            p.next();
            // Unary operator + is a no-op.
            let expr = parse_expr_unary(p)?;
            Ok(expr)
        }
        Some(Token::Minus) => match p.next() {
            Some(Token::Integer(buf)) => {
                let (valid, parsed_int) = parse_integer(buf);
                assert!(valid);
                let expr = match parsed_int {
                    ParseIntegerResult::Integer(v) => Expr::Integer(-v),
                    ParseIntegerResult::MaxPlusOne => Expr::Integer(i64::MIN),
                    ParseIntegerResult::TooBig(_) => {
                        let (valid, pure_integer, d) = parse_float(buf);
                        assert!(valid);
                        assert!(pure_integer);
                        Expr::Real(-d)
                    }
                    ParseIntegerResult::Empty => {
                        unreachable!("token integer must contain at least 1 digits only")
                    }
                };
                p.next();
                Ok(expr)
            }
            Some(Token::Float(buf)) => {
                let (valid, pure_integer, d) = parse_float(buf);
                assert!(valid);
                assert!(!pure_integer);
                p.next();
                Ok(Expr::Real(-d))
            }
            _ => {
                let expr = parse_expr_unary(p)?;
                Ok(Expr::UnaryOperator {
                    operator: UnaryOp::Minus,
                    expr: Box::new(expr),
                })
            }
        },
        _ => parse_expr_primitive(p),
    }
}

fn parse_expr_primitive<'a>(p: &mut Parser<'a>) -> Result<'a, Expr<'a>> {
    let expr = match p.peek() {
        Some(Token::Identifier(id)) => Expr::Column(*id),
        Some(Token::Cast) => {
            let Some(Token::LeftParen) = p.next() else {
                return Err(p.error("no cast left paren"));
            };
            p.next();

            let expr = parse_expr(p)?;

            let Some(Token::As) = p.peek() else {
                return Err(p.error("no cast as"));
            };
            p.next();

            let type_name = parse_type_name(p)?;

            let Some(Token::RightParen) = p.peek() else {
                return Err(p.error("no cast right paren"));
            };

            Expr::Cast {
                expr: Box::new(expr),
                type_name,
            }
        }
        Some(Token::Null) => Expr::Null,
        Some(Token::Integer(buf)) => {
            let (valid, parsed_int) = parse_integer(buf);
            assert!(valid);
            match parsed_int {
                ParseIntegerResult::Integer(v) => Expr::Integer(v),
                ParseIntegerResult::MaxPlusOne | ParseIntegerResult::TooBig(_) => {
                    let (valid, pure_integer, d) = parse_float(buf);
                    assert!(valid);
                    assert!(pure_integer);
                    Expr::Real(d)
                }
                ParseIntegerResult::Empty => {
                    unreachable!("token integer must contain at least 1 digits only")
                }
            }
        }
        Some(Token::Float(buf)) => {
            let (valid, pure_integer, d) = parse_float(buf);
            assert!(valid);
            assert!(!pure_integer);
            Expr::Real(d)
        }
        Some(Token::String(text)) => Expr::Text(*text),
        Some(Token::Blob(hex)) => Expr::Blob(*hex),
        _ => return Err(p.error("no expr")),
    };
    p.next();

    Ok(expr)
}

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! assert_parser {
        ($parse_fn:ident, $input:expr, $size:expr, $expected:expr) => {
            let mut parser = Parser::new($input);
            let r = $parse_fn(&mut parser);
            assert!(r.is_ok());
            assert_eq!(r.unwrap(), $expected);
            assert_eq!(parser.n_consumed(), $size);
        };
    }

    #[test]
    fn test_expect_semicolon() {
        assert_parser!(expect_semicolon, b";  ", 3, ());
        assert_parser!(expect_semicolon, b";  a  ", 3, ());
        assert_parser!(expect_semicolon, b"   ;  ", 6, ());

        let mut parser = Parser::new(b"     ");
        let r = expect_semicolon(&mut parser);
        assert!(r.is_err());
        assert_eq!(r.unwrap_err().cursor(), 5);

        let mut parser = Parser::new(b"");
        let r = expect_semicolon(&mut parser);
        assert!(r.is_err());
        assert_eq!(r.unwrap_err().cursor(), 0);
    }

    #[test]
    fn test_expect_no_more_token() {
        let parser = Parser::new(b"");
        let r = expect_no_more_token(&parser);
        assert!(r.is_ok());
        assert_eq!(parser.n_consumed(), 0);

        let parser = Parser::new(b"    ");
        let r = expect_no_more_token(&parser);
        assert!(r.is_ok());
        assert_eq!(parser.n_consumed(), 4);

        let parser = Parser::new(b"    ;  ");
        let r = expect_no_more_token(&parser);
        assert!(r.is_err());
        assert_eq!(r.unwrap_err().cursor(), 4);
    }

    #[test]
    fn test_parse_create_table() {
        let input = b"create table foo (id integer primary key, name text, real real, \"blob\" blob, `empty` null,[no_type])";
        let mut parser = Parser::new(input);
        let create_table = parse_create_table(&mut parser).unwrap();
        assert_eq!(parser.n_consumed(), input.len());
        assert_eq!(create_table.table_name, b"foo".as_slice().into());
        assert_eq!(
            create_table.columns,
            vec![
                ColumnDef {
                    name: b"id".as_slice().into(),
                    type_name: vec![b"integer".as_slice().into()],
                    constraints: vec![ColumnConstraint::PrinaryKey],
                },
                ColumnDef {
                    name: b"name".as_slice().into(),
                    type_name: vec![b"text".as_slice().into()],
                    constraints: vec![],
                },
                ColumnDef {
                    name: b"real".as_slice().into(),
                    type_name: vec![b"real".as_slice().into()],
                    constraints: vec![],
                },
                ColumnDef {
                    name: b"\"blob\"".as_slice().into(),
                    type_name: vec![b"blob".as_slice().into()],
                    constraints: vec![],
                },
                ColumnDef {
                    name: b"`empty`".as_slice().into(),
                    type_name: vec![b"null".as_slice().into()],
                    constraints: vec![],
                },
                ColumnDef {
                    name: b"no_type".as_slice().into(),
                    type_name: vec![],
                    constraints: vec![],
                },
            ]
        );
    }

    #[test]
    fn test_parse_create_table_type_name() {
        let input = b"create table foo (col1 type type primary key, col2 Varint(10), col3 [Float](+10), col4 \"test\"(-10.0), col5 null(0), col6 `blob```(1,+2))";
        let mut parser = Parser::new(input);
        let create_table = parse_create_table(&mut parser).unwrap();
        assert_eq!(parser.n_consumed(), input.len());
        assert_eq!(create_table.table_name, b"foo".as_slice().into());
        assert_eq!(create_table.columns.len(), 6);
        assert_eq!(
            create_table.columns[0].type_name,
            vec![b"type".as_slice().into(), b"type".as_slice().into()]
        );
        assert_eq!(
            create_table.columns[1].type_name,
            vec![b"Varint".as_slice().into()]
        );
        assert_eq!(
            create_table.columns[2].type_name,
            vec![b"Float".as_slice().into()]
        );
        assert_eq!(
            create_table.columns[3].type_name,
            vec![b"\"test\"".as_slice().into()]
        );
        assert_eq!(
            create_table.columns[4].type_name,
            vec![b"null".as_slice().into()]
        );
        assert_eq!(
            create_table.columns[5].type_name,
            vec![b"`blob```".as_slice().into()]
        );
    }

    #[test]
    fn test_parse_create_table_constraints() {
        let input = b"create table foo (col1 type type collate binary primary key collate nocase, col2 collate rtrim, col3 collate \"RTRIM\")";
        let mut parser = Parser::new(input);
        let create_table = parse_create_table(&mut parser).unwrap();
        assert_eq!(parser.n_consumed(), input.len());
        assert_eq!(
            create_table.columns[0].constraints,
            vec![
                ColumnConstraint::Collate(b"binary".as_slice().into()),
                ColumnConstraint::PrinaryKey,
                ColumnConstraint::Collate(b"nocase".as_slice().into())
            ]
        );
        assert_eq!(
            create_table.columns[1].constraints,
            vec![ColumnConstraint::Collate(b"rtrim".as_slice().into()),]
        );
        assert_eq!(
            create_table.columns[2].constraints,
            vec![ColumnConstraint::Collate(b"\"RTRIM\"".as_slice().into()),]
        );
    }

    #[test]
    fn test_parse_create_table_with_extra() {
        let input = b"create table Foo (Id, Name)abc ";
        let mut parser = Parser::new(input);
        let create_table = parse_create_table(&mut parser).unwrap();
        assert_eq!(parser.n_consumed(), input.len() - 4);
        assert_eq!(create_table.table_name, b"Foo".as_slice().into());
        assert_eq!(
            create_table.columns,
            vec![
                ColumnDef {
                    name: b"Id".as_slice().into(),
                    type_name: Vec::new(),
                    constraints: vec![],
                },
                ColumnDef {
                    name: b"Name".as_slice().into(),
                    type_name: Vec::new(),
                    constraints: vec![],
                }
            ]
        );
    }

    #[test]
    fn test_parse_create_table_fail() {
        // no column def.
        let r = parse_create_table(&mut Parser::new(b"create table foo ()"));
        assert!(r.is_err());
        assert_eq!(r.unwrap_err().cursor(), 18);
        // no right paren.
        let r = parse_create_table(&mut Parser::new(b"create table foo (id, name "));
        assert!(r.is_err());
        assert_eq!(r.unwrap_err().cursor(), 27);
        // primary without key.
        let r = parse_create_table(&mut Parser::new(b"create table foo (id primary, name)"));
        assert!(r.is_err());
        assert_eq!(r.unwrap_err().cursor(), 28);
        // key without primary.
        let r = parse_create_table(&mut Parser::new(b"create table foo (id key, name)"));
        assert!(r.is_err());
        assert_eq!(r.unwrap_err().cursor(), 21);
    }

    #[test]
    fn test_parse_create_index() {
        let input = b"create index foo on bar (col1, col2,col3)";
        let mut parser = Parser::new(input);
        let create_index = parse_create_index(&mut parser).unwrap();
        assert_eq!(parser.n_consumed(), input.len());
        assert_eq!(create_index.index_name, b"foo".as_slice().into());
        assert_eq!(create_index.table_name, b"bar".as_slice().into());
        assert_eq!(
            create_index.columns,
            vec![
                IndexedColumn {
                    name: b"col1".as_slice().into()
                },
                IndexedColumn {
                    name: b"col2".as_slice().into()
                },
                IndexedColumn {
                    name: b"col3".as_slice().into()
                },
            ]
        );
    }

    #[test]
    fn test_parse_create_index_with_extra() {
        let input = b"create index fOo on bAR (Col1,cOL2)abc ";
        let mut parser = Parser::new(input);
        let create_index = parse_create_index(&mut parser).unwrap();
        assert_eq!(parser.n_consumed(), input.len() - 4);
        assert_eq!(create_index.index_name, b"fOo".as_slice().into());
        assert_eq!(create_index.table_name, b"bAR".as_slice().into());
        assert_eq!(
            create_index.columns,
            vec![
                IndexedColumn {
                    name: b"Col1".as_slice().into()
                },
                IndexedColumn {
                    name: b"cOL2".as_slice().into()
                },
            ]
        );
    }

    #[test]
    fn test_parse_create_index_fail() {
        // no right paren.
        let r = parse_create_index(&mut Parser::new(b"create index foo on bar (id, name "));
        assert!(r.is_err());
        assert_eq!(r.unwrap_err().cursor(), 34);
    }

    #[test]
    fn test_parse_select_all() {
        let input = b"select * from foo";
        let mut parser = Parser::new(input);
        let select = parse_select(&mut parser).unwrap();
        assert_eq!(parser.n_consumed(), input.len());
        assert_eq!(select.table_name, b"foo".as_slice().into());
        assert_eq!(select.columns, vec![ResultColumn::All]);
    }

    #[test]
    fn test_parse_select_columns() {
        let input = b"select id,name,*,col as col2, col3 col4, 10, 'text' as col5, col = 11, col2 < col3 as col6 from foo";
        let mut parser = Parser::new(input);
        let select = parse_select(&mut parser).unwrap();
        assert_eq!(parser.n_consumed(), input.len());
        assert_eq!(select.table_name, b"foo".as_slice().into());
        assert_eq!(
            select.columns,
            vec![
                ResultColumn::Expr((Expr::Column(b"id".as_slice().into()), None)),
                ResultColumn::Expr((Expr::Column(b"name".as_slice().into()), None)),
                ResultColumn::All,
                ResultColumn::Expr((
                    Expr::Column(b"col".as_slice().into()),
                    Some(b"col2".as_slice().into())
                )),
                ResultColumn::Expr((
                    Expr::Column(b"col3".as_slice().into()),
                    Some(b"col4".as_slice().into())
                )),
                ResultColumn::Expr((Expr::Integer(10), None)),
                ResultColumn::Expr((
                    Expr::Text(b"'text'".as_slice().into()),
                    Some(b"col5".as_slice().into())
                )),
                ResultColumn::Expr((
                    Expr::BinaryOperator {
                        operator: BinaryOp::Compare(CompareOp::Eq),
                        left: Box::new(Expr::Column(b"col".as_slice().into())),
                        right: Box::new(Expr::Integer(11)),
                    },
                    None
                )),
                ResultColumn::Expr((
                    Expr::BinaryOperator {
                        operator: BinaryOp::Compare(CompareOp::Lt),
                        left: Box::new(Expr::Column(b"col2".as_slice().into())),
                        right: Box::new(Expr::Column(b"col3".as_slice().into())),
                    },
                    Some(b"col6".as_slice().into())
                ))
            ]
        );
    }

    #[test]
    fn test_parse_select_table_all() {
        let input = b"select bar.* from foo";
        let mut parser = Parser::new(input);
        let select = parse_select(&mut parser).unwrap();
        assert_eq!(parser.n_consumed(), input.len());
        assert_eq!(select.table_name, b"foo".as_slice().into());
        assert_eq!(
            select.columns,
            vec![ResultColumn::AllOfTable(b"bar".as_slice().into()),]
        );
    }

    #[test]
    fn test_parse_select_where() {
        let input = b"select * from foo where id = 5";
        let mut parser = Parser::new(input);
        let select = parse_select(&mut parser).unwrap();
        assert_eq!(parser.n_consumed(), input.len());
        assert_eq!(select.table_name, b"foo".as_slice().into());
        assert_eq!(select.columns, vec![ResultColumn::All,]);
        assert!(select.filter.is_some());
        assert_eq!(
            select.filter.unwrap(),
            Expr::BinaryOperator {
                operator: BinaryOp::Compare(CompareOp::Eq),
                left: Box::new(Expr::Column(b"id".as_slice().into())),
                right: Box::new(Expr::Integer(5)),
            }
        );
    }

    #[test]
    fn test_parse_select_fail() {
        // no expr after comma.
        let r = parse_select(&mut Parser::new(b"select col, from foo"));
        assert!(r.is_err());
        assert_eq!(r.unwrap_err().cursor(), 12);
        // no table name.
        let r = parse_select(&mut Parser::new(b"select col from ;"));
        assert!(r.is_err());
        assert_eq!(r.unwrap_err().cursor(), 16);
    }

    #[test]
    fn test_parse_insert() {
        assert_parser!(
            parse_insert,
            b"insert into example (col) values (1)",
            36,
            Insert {
                table_name: b"example".as_slice().into(),
                columns: vec![b"col".as_slice().into()],
                values: vec![vec![Expr::Integer(1)]],
            }
        );
        assert_parser!(
            parse_insert,
            b"insert into example2 (col, col2) values (1, 2)a",
            46,
            Insert {
                table_name: b"example2".as_slice().into(),
                columns: vec![b"col".as_slice().into(), b"col2".as_slice().into()],
                values: vec![vec![Expr::Integer(1), Expr::Integer(2)]],
            }
        );
        assert_parser!(
            parse_insert,
            b"insert into example2 (col, col2) values (1, 2), (3, 4)a",
            54,
            Insert {
                table_name: b"example2".as_slice().into(),
                columns: vec![b"col".as_slice().into(), b"col2".as_slice().into()],
                values: vec![
                    vec![Expr::Integer(1), Expr::Integer(2)],
                    vec![Expr::Integer(3), Expr::Integer(4)]
                ],
            }
        );
    }

    #[test]
    fn test_parse_insert_fail() {
        // no expr right paren.
        let r = parse_insert(&mut Parser::new(b"insert into example (col values (1)"));
        assert!(r.is_err());
        assert_eq!(r.unwrap_err().cursor(), 25);
        // no table name.
        let r = parse_insert(&mut Parser::new(b"insert into (col) values (1)"));
        assert!(r.is_err());
        assert_eq!(r.unwrap_err().cursor(), 12);
    }

    #[test]
    fn test_parse_expr_literal_value() {
        // Parse null
        assert_parser!(parse_expr, b"null", 4, Expr::Null);

        // Parse integer
        assert_parser!(parse_expr, b"123456789a", 9, Expr::Integer(123456789));
        assert_parser!(parse_expr, b"00123456789a", 11, Expr::Integer(123456789));
        assert_parser!(parse_expr, b"00000000000000000001a", 20, Expr::Integer(1));
        assert_parser!(
            parse_expr,
            b"9223372036854775807",
            19,
            Expr::Integer(9223372036854775807)
        );
        assert_parser!(
            parse_expr,
            b"000000000000000000009223372036854775807",
            39,
            Expr::Integer(9223372036854775807)
        );
        // integer -> float fallback
        assert_parser!(
            parse_expr,
            b"9223372036854775808",
            19,
            Expr::Real(9223372036854775808.0)
        );
        assert_parser!(
            parse_expr,
            b"9999999999999999999",
            19,
            Expr::Real(9999999999999999999.0)
        );
        assert_parser!(
            parse_expr,
            b"99999999999999999999a",
            20,
            Expr::Real(99999999999999999999.0)
        );

        // Parse float
        assert_parser!(parse_expr, b".1", 2, Expr::Real(0.1));
        assert_parser!(parse_expr, b"1.", 2, Expr::Real(1.0));
        assert_parser!(parse_expr, b"1.01", 4, Expr::Real(1.01));
        assert_parser!(parse_expr, b"1e1", 3, Expr::Real(10.0));
        assert_parser!(parse_expr, b"1e-1", 4, Expr::Real(0.1));

        // Parse string
        assert_parser!(
            parse_expr,
            b"'hello'",
            7,
            Expr::Text(b"'hello'".as_slice().into())
        );
        assert_parser!(
            parse_expr,
            b"'hel''lo'",
            9,
            Expr::Text(b"'hel''lo'".as_slice().into())
        );

        // Parse blob
        assert_parser!(
            parse_expr,
            b"x'0123456789abcdef'",
            19,
            Expr::Blob(b"0123456789abcdef".as_slice().into())
        );
        assert_parser!(
            parse_expr,
            b"X'0123456789abcdef'",
            19,
            Expr::Blob(b"0123456789abcdef".as_slice().into())
        );
    }

    #[test]
    fn test_parse_expr_column() {
        assert_parser!(
            parse_expr,
            b"foo",
            3,
            Expr::Column(b"foo".as_slice().into())
        );
        assert_parser!(
            parse_expr,
            b"\"foo\"",
            5,
            Expr::Column(b"\"foo\"".as_slice().into())
        );
    }

    #[test]
    fn test_parse_expr_cast() {
        assert_parser!(
            parse_expr,
            b"cast(100as text)",
            16,
            Expr::Cast {
                expr: Box::new(Expr::Integer(100)),
                type_name: vec![b"text".as_slice().into()],
            }
        );
        assert_parser!(
            parse_expr,
            b"cast ( '100' as integer)",
            24,
            Expr::Cast {
                expr: Box::new(Expr::Text(b"'100'".as_slice().into())),
                type_name: vec![b"integer".as_slice().into()],
            }
        );
        assert_parser!(
            parse_expr,
            b"cast (col = 100 as integer)",
            27,
            Expr::Cast {
                expr: Box::new(Expr::BinaryOperator {
                    operator: BinaryOp::Compare(CompareOp::Eq),
                    left: Box::new(Expr::Column(b"col".as_slice().into())),
                    right: Box::new(Expr::Integer(100))
                }),
                type_name: vec![b"integer".as_slice().into()],
            }
        );
    }

    #[test]
    fn test_parse_expr_unary_operator() {
        assert_parser!(
            parse_expr,
            b"+foo",
            4,
            Expr::Column(b"foo".as_slice().into())
        );
        assert_parser!(
            parse_expr,
            b"-foo",
            4,
            Expr::UnaryOperator {
                operator: UnaryOp::Minus,
                expr: Box::new(Expr::Column(b"foo".as_slice().into()))
            }
        );
        assert_parser!(
            parse_expr,
            b"~foo",
            4,
            Expr::UnaryOperator {
                operator: UnaryOp::BitNot,
                expr: Box::new(Expr::Column(b"foo".as_slice().into()))
            }
        );
        assert_parser!(
            parse_expr,
            b"~~foo",
            5,
            Expr::UnaryOperator {
                operator: UnaryOp::BitNot,
                expr: Box::new(Expr::UnaryOperator {
                    operator: UnaryOp::BitNot,
                    expr: Box::new(Expr::Column(b"foo".as_slice().into()))
                })
            }
        );
        assert_parser!(
            parse_expr,
            b"-+-+-foo",
            8,
            Expr::UnaryOperator {
                operator: UnaryOp::Minus,
                expr: Box::new(Expr::UnaryOperator {
                    operator: UnaryOp::Minus,
                    expr: Box::new(Expr::UnaryOperator {
                        operator: UnaryOp::Minus,
                        expr: Box::new(Expr::Column(b"foo".as_slice().into()))
                    })
                })
            }
        );
        assert_parser!(parse_expr, b"+123", 4, Expr::Integer(123));
        assert_parser!(parse_expr, b"+ 123", 5, Expr::Integer(123));
        assert_parser!(parse_expr, b"-123", 4, Expr::Integer(-123));
        assert_parser!(parse_expr, b"- 123", 5, Expr::Integer(-123));
        assert_parser!(
            parse_expr,
            b"-9223372036854775808",
            20,
            Expr::Integer(-9223372036854775808)
        );
        assert_parser!(
            parse_expr,
            b"-+-123",
            6,
            Expr::UnaryOperator {
                operator: UnaryOp::Minus,
                expr: Box::new(Expr::Integer(-123))
            }
        );
        assert_parser!(parse_expr, b"+123.4", 6, Expr::Real(123.4));
        assert_parser!(parse_expr, b"-123.4", 6, Expr::Real(-123.4));
        assert_parser!(
            parse_expr,
            b"-+-123.4",
            8,
            Expr::UnaryOperator {
                operator: UnaryOp::Minus,
                expr: Box::new(Expr::Real(-123.4))
            }
        );
        assert_parser!(
            parse_expr,
            b"+'abc'",
            6,
            Expr::Text(b"'abc'".as_slice().into())
        );
        assert_parser!(
            parse_expr,
            b"-'abc'",
            6,
            Expr::UnaryOperator {
                operator: UnaryOp::Minus,
                expr: Box::new(Expr::Text(b"'abc'".as_slice().into()))
            }
        );
        assert_parser!(
            parse_expr,
            b"-abc",
            4,
            Expr::UnaryOperator {
                operator: UnaryOp::Minus,
                expr: Box::new(Expr::Column(b"abc".as_slice().into()))
            }
        );
        assert_parser!(
            parse_expr,
            b"~-abc",
            5,
            Expr::UnaryOperator {
                operator: UnaryOp::BitNot,
                expr: Box::new(Expr::UnaryOperator {
                    operator: UnaryOp::Minus,
                    expr: Box::new(Expr::Column(b"abc".as_slice().into()))
                })
            }
        );
    }

    #[test]
    fn test_parse_expr_collate() {
        assert_parser!(
            parse_expr,
            b"abc COLLATE binary",
            18,
            Expr::Collate {
                expr: Box::new(Expr::Column(b"abc".as_slice().into())),
                collation_name: b"binary".as_slice().into()
            }
        );
        assert_parser!(
            parse_expr,
            b"'abc' COLLATE \"nocase\"",
            22,
            Expr::Collate {
                expr: Box::new(Expr::Text(b"'abc'".as_slice().into())),
                collation_name: b"\"nocase\"".as_slice().into()
            }
        );
        assert_parser!(
            parse_expr,
            b"-abc COLLATE rtrim",
            18,
            Expr::Collate {
                expr: Box::new(Expr::UnaryOperator {
                    operator: UnaryOp::Minus,
                    expr: Box::new(Expr::Column(b"abc".as_slice().into()))
                }),
                collation_name: b"rtrim".as_slice().into()
            }
        );
        assert_parser!(
            parse_expr,
            b"abc COLLATE binary COLLATE nocase COLLATE rtrim",
            47,
            Expr::Collate {
                expr: Box::new(Expr::Column(b"abc".as_slice().into())),
                collation_name: b"rtrim".as_slice().into()
            }
        );
    }

    #[test]
    fn test_parse_expr_concat() {
        assert_parser!(
            parse_expr,
            b"'abc' || 2",
            10,
            Expr::BinaryOperator {
                operator: BinaryOp::Concat,
                left: Box::new(Expr::Text(b"'abc'".as_slice().into())),
                right: Box::new(Expr::Integer(2)),
            }
        );
        assert_parser!(
            parse_expr,
            b"-1 || 2 || -abc",
            15,
            Expr::BinaryOperator {
                operator: BinaryOp::Concat,
                left: Box::new(Expr::BinaryOperator {
                    operator: BinaryOp::Concat,
                    left: Box::new(Expr::Integer(-1)),
                    right: Box::new(Expr::Integer(2)),
                }),
                right: Box::new(Expr::UnaryOperator {
                    operator: UnaryOp::Minus,
                    expr: Box::new(Expr::Column(b"abc".as_slice().into()))
                }),
            }
        );
    }

    #[test]
    fn test_parse_expr_compare() {
        assert_parser!(
            parse_expr,
            b"-1 < 2",
            6,
            Expr::BinaryOperator {
                operator: BinaryOp::Compare(CompareOp::Lt),
                left: Box::new(Expr::Integer(-1)),
                right: Box::new(Expr::Integer(2)),
            }
        );
        assert_parser!(
            parse_expr,
            b"-1 <= 2",
            7,
            Expr::BinaryOperator {
                operator: BinaryOp::Compare(CompareOp::Le),
                left: Box::new(Expr::Integer(-1)),
                right: Box::new(Expr::Integer(2)),
            }
        );
        assert_parser!(
            parse_expr,
            b"-1 > 2",
            6,
            Expr::BinaryOperator {
                operator: BinaryOp::Compare(CompareOp::Gt),
                left: Box::new(Expr::Integer(-1)),
                right: Box::new(Expr::Integer(2)),
            }
        );
        assert_parser!(
            parse_expr,
            b"-1 >= 2",
            7,
            Expr::BinaryOperator {
                operator: BinaryOp::Compare(CompareOp::Ge),
                left: Box::new(Expr::Integer(-1)),
                right: Box::new(Expr::Integer(2)),
            }
        );
        assert_parser!(
            parse_expr,
            b"-1 >= 2 >= -abc",
            15,
            Expr::BinaryOperator {
                operator: BinaryOp::Compare(CompareOp::Ge),
                left: Box::new(Expr::BinaryOperator {
                    operator: BinaryOp::Compare(CompareOp::Ge),
                    left: Box::new(Expr::Integer(-1)),
                    right: Box::new(Expr::Integer(2)),
                }),
                right: Box::new(Expr::UnaryOperator {
                    operator: UnaryOp::Minus,
                    expr: Box::new(Expr::Column(b"abc".as_slice().into()))
                }),
            }
        );
    }

    #[test]
    fn test_parse_expr_eq() {
        assert_parser!(
            parse_expr,
            b"-1 = 2",
            6,
            Expr::BinaryOperator {
                operator: BinaryOp::Compare(CompareOp::Eq),
                left: Box::new(Expr::Integer(-1)),
                right: Box::new(Expr::Integer(2)),
            }
        );
        assert_parser!(
            parse_expr,
            b"-1 == 2",
            7,
            Expr::BinaryOperator {
                operator: BinaryOp::Compare(CompareOp::Eq),
                left: Box::new(Expr::Integer(-1)),
                right: Box::new(Expr::Integer(2)),
            }
        );
        assert_parser!(
            parse_expr,
            b"-1 != 2",
            7,
            Expr::BinaryOperator {
                operator: BinaryOp::Compare(CompareOp::Ne),
                left: Box::new(Expr::Integer(-1)),
                right: Box::new(Expr::Integer(2)),
            }
        );
        assert_parser!(
            parse_expr,
            b"-1 <> 2",
            7,
            Expr::BinaryOperator {
                operator: BinaryOp::Compare(CompareOp::Ne),
                left: Box::new(Expr::Integer(-1)),
                right: Box::new(Expr::Integer(2)),
            }
        );
        assert_parser!(
            parse_expr,
            b"1 = 2 = 3",
            9,
            Expr::BinaryOperator {
                operator: BinaryOp::Compare(CompareOp::Eq),
                left: Box::new(Expr::BinaryOperator {
                    operator: BinaryOp::Compare(CompareOp::Eq),
                    left: Box::new(Expr::Integer(1)),
                    right: Box::new(Expr::Integer(2)),
                }),
                right: Box::new(Expr::Integer(3)),
            }
        );
    }

    #[test]
    fn test_parse_expr_operators() {
        assert_parser!(
            parse_expr,
            b"1 || -2 COLLATE nocase",
            22,
            Expr::BinaryOperator {
                operator: BinaryOp::Concat,
                left: Box::new(Expr::Integer(1)),
                right: Box::new(Expr::Collate {
                    expr: Box::new(Expr::Integer(-2)),
                    collation_name: b"nocase".as_slice().into()
                }),
            }
        );
        assert_parser!(
            parse_expr,
            b"1 || 2 < 3 || 4",
            15,
            Expr::BinaryOperator {
                operator: BinaryOp::Compare(CompareOp::Lt),
                left: Box::new(Expr::BinaryOperator {
                    operator: BinaryOp::Concat,
                    left: Box::new(Expr::Integer(1)),
                    right: Box::new(Expr::Integer(2)),
                }),
                right: Box::new(Expr::BinaryOperator {
                    operator: BinaryOp::Concat,
                    left: Box::new(Expr::Integer(3)),
                    right: Box::new(Expr::Integer(4)),
                }),
            }
        );
        assert_parser!(
            parse_expr,
            b"1 < 2 = 3 < 4",
            13,
            Expr::BinaryOperator {
                operator: BinaryOp::Compare(CompareOp::Eq),
                left: Box::new(Expr::BinaryOperator {
                    operator: BinaryOp::Compare(CompareOp::Lt),
                    left: Box::new(Expr::Integer(1)),
                    right: Box::new(Expr::Integer(2)),
                }),
                right: Box::new(Expr::BinaryOperator {
                    operator: BinaryOp::Compare(CompareOp::Lt),
                    left: Box::new(Expr::Integer(3)),
                    right: Box::new(Expr::Integer(4)),
                }),
            }
        );
        assert_parser!(
            parse_expr,
            b"1 < 2 = 3 < 4 = 5",
            17,
            Expr::BinaryOperator {
                operator: BinaryOp::Compare(CompareOp::Eq),
                left: Box::new(Expr::BinaryOperator {
                    operator: BinaryOp::Compare(CompareOp::Eq),
                    left: Box::new(Expr::BinaryOperator {
                        operator: BinaryOp::Compare(CompareOp::Lt),
                        left: Box::new(Expr::Integer(1)),
                        right: Box::new(Expr::Integer(2)),
                    }),
                    right: Box::new(Expr::BinaryOperator {
                        operator: BinaryOp::Compare(CompareOp::Lt),
                        left: Box::new(Expr::Integer(3)),
                        right: Box::new(Expr::Integer(4)),
                    }),
                }),
                right: Box::new(Expr::Integer(5)),
            }
        );
    }
}
