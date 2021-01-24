#[macro_use]
extern crate lang_macros;

use clap::clap_app;
use std::io::ErrorKind;
use std::fs;

use crate::ast::Attribute;
use lang_stuff::Parse;

mod ast;

fn parse(input: &str) -> std::io::Result<Attribute> {
    match Attribute::parse(input) {
        Ok((_,ast)) => Ok(ast),
        Err(e) => Err(std::io::Error::new(ErrorKind::Other, e))
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
