mod standard;
mod valid;

use valid::FuncType;

fn main() {
    let mut ctx = standard::std_context();
    ctx.add_opaque_type("Foo", &[
        ("Foo::four", FuncType{res:"Foo".to_owned(), args:vec![]}),
        ("Foo::six", FuncType{res:"Foo".to_owned(), args:vec![]}),
        ("Foo::to_nat", FuncType{res:"BigUint".to_owned(), args:vec!["Foo".to_owned()]}),
    ]).unwrap();
    println!("{:?}", ctx.nat("BigUint",42u8.into()));
    println!("{:?}", ctx.structure("()", &[]));
    let four = ctx.call("Foo::four", &[]).unwrap();
    let four_n = ctx.call("Foo::to_nat", &[four]).unwrap();
    println!("{:?}", four_n);
}
