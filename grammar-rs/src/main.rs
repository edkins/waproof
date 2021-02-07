#[macro_use]
extern crate lang_macros;

use clap::clap_app;
use std::fs;

use crate::ast::{Expansion,Module};
use lang_stuff::{Error,Parse};

mod ast;
mod query;
mod semantics;

fn parse<T:Parse>(input: &str) -> std::io::Result<T> {
    match T::parse(input) {
        Ok((_,ast)) => Ok(ast),
        Err(nom::Err::Incomplete(_)) => Err(Error{msg:"Incomplete".to_owned(), positions:vec![]}.into()),
        Err(nom::Err::Error(e)) | Err(nom::Err::Failure(e)) => Err(e.into()),
    }
}

fn main() -> std::io::Result<()> {
    let matches = clap_app!(lang_rs =>
        (@arg INPUT: +required "Input file to process")
    ).get_matches();

    let input = matches.value_of("INPUT").unwrap();

    let ast = parse::<Module>(&fs::read_to_string(input)?)?;
    let script = ast.to_script()?;

    let mut rl = rustyline::Editor::<()>::new();
    loop {
        match rl.readline("?- ") {
            Ok(line) => {
                rl.add_history_entry(&line);
                match parse::<Expansion>(&line) {
                    Ok(line_ast) => {
                        match line_ast.to_query(&script) {
                            Ok(line_query) => {
                                match line_query.eval(&script) {
                                    Ok(b) => println!("{}", b),
                                    Err(e) => println!("{}", e),
                                }
                            }
                            Err(e) => println!("{}", e)
                        }
                    }
                    Err(e) => println!("{}", e)
                }
            }
            Err(_) => {break;}
        }
    }

    Ok(())
}
