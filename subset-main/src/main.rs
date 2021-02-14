#[macro_use]
extern crate subset_macros;

use subset_stuff::PaLift;

#[derive(PaLift)]
enum Foo {
    Bar(bool),
    Baz(bool,bool),
}

fn main() {
    println!("{:?}", Foo::Bar(true).pa_lift());
}
