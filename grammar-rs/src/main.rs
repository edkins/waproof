#[macro_use]
extern crate lang_macros;

use clap::clap_app;
use std::fs;

use crate::ast::Module;
use lang_stuff::{Error,Parse};

mod ast;

fn parse(input: &str) -> std::io::Result<Module> {
    match Module::parse(input) {
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

    let ast = parse(&fs::read_to_string(input)?)?;

    println!("{}", ast);

    Ok(())
}
