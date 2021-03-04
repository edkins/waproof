use crate::pa_formula::{Expr, Formula, SyntaxError};

impl Expr {
    pub fn subst(&self, x: &str, value: &Expr) -> Expr{
        match self {
            Expr::Var(y) => {
                if y == x {
                    value.clone()
                } else {
                    Expr::var(y)
                }
            }
            Expr::Z => Expr::z(),
            Expr::S(e) => e.subst(x, value).s(),
            Expr::Add(a, b) => a.subst(x, value).add(b.subst(x, value)),
            Expr::Mul(a, b) => a.subst(x, value).mul(b.subst(x, value)),
        }
    }
}

impl Formula {
    pub fn subst(&self, x: &str, value: &Expr) -> Result<Formula, SyntaxError> {
        Ok(match self {
            Formula::False => Formula::falsehood(),
            Formula::Eq(a, b) => a.subst(x, value).eq(b.subst(x, value)),
            Formula::Imp(p, q) => p.subst(x, value)?.imp(q.subst(x, value)?),
            Formula::ForAll(y, p) => {
                if x == y {
                    return Err(SyntaxError::SubstBoundVar(y.clone()));
                }
                if value.has_free(y) {
                    return Err(SyntaxError::SubstForBoundVar(y.clone()));
                }
                p.subst(x, value)?.forall(&y)
            }
            Formula::Memo(m) => m.formula().subst(x, value)?.memo()?,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::pa_formula::Expr;

    #[test]
    fn simple_formula_subst_zero() {
        let f = Expr::var("x").eq(Expr::var("y"));
        let g = f.subst("x", &Expr::z()).unwrap();
        let expected = Expr::z().eq(Expr::var("y"));
        assert_eq!(expected, g);
    }

    #[test]
    fn simple_formula_subst_zero_twice() {
        let f = Expr::var("x").eq(Expr::var("x"));
        let g = f.subst("x", &Expr::z()).unwrap();
        let expected = Expr::z().eq(Expr::z());
        assert_eq!(expected, g);
    }

    #[test]
    fn simple_formula_subst_var() {
        let f = Expr::var("x").eq(Expr::var("y"));
        let g = f.subst("x", &Expr::var("z")).unwrap();
        let expected = Expr::var("z").eq(Expr::var("y"));
        assert_eq!(expected, g);
    }

    #[test]
    fn simple_formula_subst_self() {
        let f = Expr::var("x").eq(Expr::var("y"));
        let g = f.clone().subst("x", &Expr::var("x")).unwrap();
        assert_eq!(f, g);
    }

    #[test]
    fn simple_formula_subst_missing() {
        let f = Expr::var("y").eq(Expr::var("y"));
        let g = f.clone().subst("x", &Expr::z()).unwrap();
        assert_eq!(f, g);
    }

    #[test]
    fn simple_formula_subst_other() {
        let f = Expr::var("x").eq(Expr::var("y"));
        let g = f.subst("x", &Expr::var("y")).unwrap();
        let expected = Expr::var("y").eq(Expr::var("y"));
        assert_eq!(expected, g);
    }

    #[test]
    fn simple_formula_subst_forall() {
        let f = Expr::var("x")
            .eq(Expr::var("y"))
            .forall("y");
        let g = f.subst("x", &Expr::z()).unwrap();
        let expected = Expr::z().eq(Expr::var("y")).forall("y");
        assert_eq!(expected, g);
    }

    #[test]
    fn simple_formula_subst_forall_invalid() {
        let f = Expr::var("x")
            .eq(Expr::var("y"))
            .forall("x");
        let g = f.subst("x", &Expr::z());
        assert!(g.is_err());
    }
}
