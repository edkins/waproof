use crate::pa_formula::{Expr, ExprVars, Formula, FormulaVars, SyntaxError};

impl Expr {
    fn subst(&self, x: &str, value: &ExprVars) -> ExprVars {
        match self {
            Expr::Var(y) => {
                if y == x {
                    value.clone()
                } else {
                    ExprVars::var(y)
                }
            }
            Expr::Z => ExprVars::z(),
            Expr::S(e) => e.subst(x, value).s(),
            Expr::Add(a, b) => a.subst(x, value).add(b.subst(x, value)),
            Expr::Mul(a, b) => a.subst(x, value).mul(b.subst(x, value)),
        }
    }
}

impl Formula {
    fn subst(&self, x: &str, value: &ExprVars) -> Result<FormulaVars, SyntaxError> {
        Ok(match self {
            Formula::False => FormulaVars::falsehood(),
            Formula::Eq(a, b) => a.subst(x, value).eq(b.subst(x, value)),
            Formula::Imp(p, q) => p.subst(x, value)?.imp(q.subst(x, value)?).unwrap(),
            Formula::ForAll(y, p) => {
                if x == y {
                    return Err(SyntaxError::SubstBoundVar(y.clone()));
                }
                if value.has_free(y) {
                    return Err(SyntaxError::SubstForBoundVar(y.clone()));
                }
                p.subst(x, value)?.forall(&y)?
            }
            Formula::Memo(m) => m.clone().subst(x, value)?.memo(),
        })
    }
}

impl ExprVars {
    pub fn has_free(&self, x: &str) -> bool {
        self.free().iter().any(|y| y == x)
    }
}

impl FormulaVars {
    pub fn has_bound(&self, x: &str) -> bool {
        self.bound().iter().any(|y| y == x)
    }

    pub fn has_free(&self, x: &str) -> bool {
        self.free().iter().any(|y| y == x)
    }

    pub fn subst(self, x: &str, value: &ExprVars) -> Result<FormulaVars, SyntaxError> {
        for y in value.free() {
            if self.has_bound(y) {
                return Err(SyntaxError::SubstForBoundVar(y.clone()));
            }
        }

        if self.has_bound(x) {
            Err(SyntaxError::SubstBoundVar(x.to_owned()))
        } else if self.has_free(x) {
            Ok(self.formula().subst(x, value)?)
        } else {
            Ok(self)
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::pa_formula::ExprVars;

    #[test]
    fn simple_formula_subst_zero() {
        let f = ExprVars::var("x").eq(ExprVars::var("y"));
        let g = f.subst("x", &ExprVars::z()).unwrap();
        let expected = ExprVars::z().eq(ExprVars::var("y"));
        assert_eq!(expected, g);
    }

    #[test]
    fn simple_formula_subst_zero_twice() {
        let f = ExprVars::var("x").eq(ExprVars::var("x"));
        let g = f.subst("x", &ExprVars::z()).unwrap();
        let expected = ExprVars::z().eq(ExprVars::z());
        assert_eq!(expected, g);
    }

    #[test]
    fn simple_formula_subst_var() {
        let f = ExprVars::var("x").eq(ExprVars::var("y"));
        let g = f.subst("x", &ExprVars::var("z")).unwrap();
        let expected = ExprVars::var("z").eq(ExprVars::var("y"));
        assert_eq!(expected, g);
    }

    #[test]
    fn simple_formula_subst_self() {
        let f = ExprVars::var("x").eq(ExprVars::var("y"));
        let g = f.clone().subst("x", &ExprVars::var("x")).unwrap();
        assert_eq!(f, g);
    }

    #[test]
    fn simple_formula_subst_missing() {
        let f = ExprVars::var("y").eq(ExprVars::var("y"));
        let g = f.clone().subst("x", &ExprVars::z()).unwrap();
        assert_eq!(f, g);
    }

    #[test]
    fn simple_formula_subst_other() {
        let f = ExprVars::var("x").eq(ExprVars::var("y"));
        let g = f.subst("x", &ExprVars::var("y")).unwrap();
        let expected = ExprVars::var("y").eq(ExprVars::var("y"));
        assert_eq!(expected, g);
    }

    #[test]
    fn simple_formula_subst_forall() {
        let f = ExprVars::var("x")
            .eq(ExprVars::var("y"))
            .forall("y")
            .unwrap();
        let g = f.subst("x", &ExprVars::z()).unwrap();
        let expected = ExprVars::z().eq(ExprVars::var("y")).forall("y").unwrap();
        assert_eq!(expected, g);
    }

    #[test]
    fn simple_formula_subst_forall_invalid() {
        let f = ExprVars::var("x")
            .eq(ExprVars::var("y"))
            .forall("x")
            .unwrap();
        let g = f.subst("x", &ExprVars::z());
        assert!(g.is_err());
    }
}
