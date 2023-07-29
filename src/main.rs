use std::env;
use std::io;
use std::io::Write;
use std::path::Path;

use prsqlite::Connection;

fn main() {
    let mut args = env::args();
    if args.len() != 2 {
        eprintln!("Usage: prsqlite [dbfile]");
        std::process::exit(1);
    }
    let file_path = args.nth(1).unwrap();
    let mut conn = Connection::open(Path::new(&file_path)).expect("open database");

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
                let mut stmt = match conn.prepare(line) {
                    Ok(stmt) => stmt,
                    Err(e) => {
                        eprintln!("{e}");
                        continue;
                    }
                };
                let mut rows = stmt.execute().expect("execute statement");
                while let Some(mut row) = rows.next().expect("next row") {
                    let columns = row.parse().expect("parse row");
                    for i in 0..columns.len() {
                        if i > 0 {
                            print!("|");
                        }
                        print!("{}", columns.get(i));
                    }
                    println!();
                }
            }
        }
    }
}
