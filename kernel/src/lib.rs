pub mod pa_axiom;
pub mod pa_convenience;
pub mod pa_formula;
pub mod pa_parse;
pub mod pa_subst;
mod wa_binary;
mod wa_type;
pub mod wa_valid;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
