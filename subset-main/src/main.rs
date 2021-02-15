mod standard;
mod valid;

fn main() {
    let ctx = standard::std_context();
    println!("{:?}", ctx.nat("BigUint",42u8.into()));
    println!("{:?}", ctx.structure("()", &[]));
}
