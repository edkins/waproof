use crate::pa_formula::{Expr, Formula, SyntaxError};

impl Expr {
    pub fn subst(&self, x: &str, value: &Expr) -> Expr {
        if !self.has_free(x) {
            return self.clone();
        }
        self.cases(
            |y| {
                if y == x {
                    value.clone()
                } else {
                    Expr::var(y)
                }
            },
            || Expr::z(),
            |a| a.subst(x, value).s(),
            |a, b| a.subst(x, value).add(b.subst(x, value)),
            |a, b| a.subst(x, value).mul(b.subst(x, value)),
        )
    }
}

impl Formula {
    pub fn subst(&self, x: &str, value: &Expr) -> Result<Formula, SyntaxError> {
        if self.has_bound(x) {
            return Err(SyntaxError::SubstBoundVar(x.to_owned()));
        }
        if !self.has_free(x) {
            return Ok(self.clone());
        }
        self.cases(
            || Ok(Formula::falsehood()),
            |a, b| Ok(a.subst(x, value).eq(b.subst(x, value))),
            |p, q| p.subst(x, value)?.imp(q.subst(x, value)?),
            |y, p| {
                if x == y {
                    return Err(SyntaxError::SubstBoundVar(y.to_owned()));
                }
                if value.has_free(y) {
                    return Err(SyntaxError::SubstForBoundVar(y.to_owned()));
                }
                p.subst(x, value)?.forall(&y)
            },
        )
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
        let f = Expr::var("x").eq(Expr::var("y")).forall("y").unwrap();
        let g = f.subst("x", &Expr::z()).unwrap();
        let expected = Expr::z().eq(Expr::var("y")).forall("y").unwrap();
        assert_eq!(expected, g);
    }

    #[test]
    fn simple_formula_subst_forall_invalid() {
        let f = Expr::var("x").eq(Expr::var("y")).forall("x").unwrap();
        let g = f.subst("x", &Expr::z());
        assert!(g.is_err());
    }
}
