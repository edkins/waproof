#[macro_use]
extern crate subset_macros;

use subset_stuff::PaLift;

#[derive(PaLift)]
struct Foo {
    bar: bool,
}

fn main() {
    println!("Hello, world! {:?}", Foo::pa_type());
}
