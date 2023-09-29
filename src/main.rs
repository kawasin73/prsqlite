use std::env;
use std::io;
use std::io::Write;
use std::path::Path;

use prsqlite::Connection;
use prsqlite::Statement;

fn main() {
    let mut args = env::args();
    if args.len() != 2 {
        eprintln!("Usage: prsqlite [dbfile]");
        std::process::exit(1);
    }
    let file_path = args.nth(1).unwrap();
    let conn = Connection::open(Path::new(&file_path)).expect("open database");

    let mut stdout = io::stdout();
    let stdin = io::stdin();
    let mut buf = String::new();

    loop {
        print!("prsqlite> ");
        stdout.flush().expect("flush stdout");
        buf.truncate(0);
        let n = stdin.read_line(&mut buf).expect("read line");
        let line = &buf[..n];
        match line.trim() {
            ".quit" | ".exit" => break,
            "" => continue,
            line => {
                let stmt = match conn.prepare(line) {
                    Ok(stmt) => stmt,
                    Err(e) => {
                        eprintln!("{e}");
                        continue;
                    }
                };
                match stmt {
                    Statement::Query(stmt) => {
                        let mut rows = stmt.query().expect("execute statement");
                        loop {
                            let row = match rows.next_row() {
                                Ok(Some(row)) => row,
                                Ok(None) => break,
                                Err(e) => {
                                    eprintln!("{e}");
                                    break;
                                }
                            };
                            let columns = row.parse().expect("parse row");
                            for i in 0..columns.len() {
                                if i > 0 {
                                    print!("|");
                                }
                                columns.get(i).display(&mut stdout).expect("display column");
                            }
                            println!();
                        }
                    }
                    Statement::Execution(stmt) => {
                        if let Err(e) = stmt.execute() {
                            eprintln!("{e}");
                        }
                    }
                }
            }
        }
    }
}
