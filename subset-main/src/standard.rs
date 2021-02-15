use crate::valid::ValidContext;

pub fn std_context() -> ValidContext {
    let mut ctx = ValidContext::empty();

    ctx.add_nat_type("BigUint").unwrap();
    ctx.add_struct_type("()", &[]).unwrap();

    ctx
}
