#[macro_use]
extern crate lang_macros;

use clap::clap_app;

mod ast;

fn main() {
    let matches = clap_app!(lang_rs =>
        (@arg INPUT: +required "Input file to process")
    ).get_matches();

    let input = matches.value_of("INPUT").unwrap();
    println!("{}", input);
}
