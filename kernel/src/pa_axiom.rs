use crate::pa_formula::{ExprVars, Formula, FormulaVars, SyntaxError};

#[derive(Debug)]
pub enum TheoremError {
    Syntax(SyntaxError),
    FreeVar(String),
    MixingFreeAndBound(String),
    BoundTwice(String),
    SubstBoundVar(String),
    NotImp,
    WrongHyp,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Theorem {
    f: FormulaVars,
}

impl From<SyntaxError> for TheoremError {
    fn from(e: SyntaxError) -> Self {
        TheoremError::Syntax(e)
    }
}

impl FormulaVars {
    fn generalize(mut self, gen: &[&str]) -> Result<Self, TheoremError> {
        for var in gen {
            self = self.forall(var)?;
        }
        if let Some(x) = self.free().get(0) {
            Err(TheoremError::FreeVar(x.clone()))
        } else {
            Ok(self)
        }
    }
}

impl Theorem {
    pub fn formula(&self) -> &FormulaVars {
        &self.f
    }

    pub fn a1(a: FormulaVars, b: FormulaVars, gen: &[&str]) -> Result<Self, TheoremError> {
        let f = a.clone().imp(b.imp(a)?)?.generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn a2(
        a: FormulaVars,
        b: FormulaVars,
        c: FormulaVars,
        gen: &[&str],
    ) -> Result<Self, TheoremError> {
        let abc = a.clone().imp(b.clone().imp(c.clone())?)?;
        let abac = a.clone().imp(b)?.imp(a.imp(c)?)?;
        let f = abc.imp(abac)?.generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn a3(a: FormulaVars, gen: &[&str]) -> Result<Self, TheoremError> {
        let f = a
            .clone()
            .imp(FormulaVars::falsehood())?
            .imp(FormulaVars::falsehood())?
            .imp(a)?
            .generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn a4(a: FormulaVars, b: FormulaVars, x: &str, gen: &[&str]) -> Result<Self, TheoremError> {
        if a.has_bound(x) || b.has_bound(x) {
            return Err(TheoremError::BoundTwice(x.to_owned()));
        }
        let f = (a.clone().imp(b.clone())?)
            .forall(x)?
            .imp(a.forall(x)?.imp(b.forall(x)?)?)?
            .generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn a5(a: FormulaVars, x: &str, gen: &[&str]) -> Result<Self, TheoremError> {
        if a.has_free(x) {
            return Err(TheoremError::MixingFreeAndBound(x.to_owned()));
        }
        if a.has_bound(x) {
            return Err(TheoremError::BoundTwice(x.to_owned()));
        }
        let f = a.clone().imp(a.forall(x)?)?.generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn a6(a: FormulaVars, x: &str, e: ExprVars, gen: &[&str]) -> Result<Self, TheoremError> {
        if a.has_bound(x) {
            return Err(TheoremError::SubstBoundVar(x.to_owned()));
        }
        let f = a.clone().forall(x)?.imp(a.subst(x, &e)?)?.generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn mp(self, other: Theorem) -> Result<Self, TheoremError> {
        if let Formula::Imp(a, b) = self.f.formula() {
            if **a == *other.f.formula() {
                let f = b.reconstitute()?;
                Ok(Theorem { f })
            } else {
                Err(TheoremError::WrongHyp)
            }
        } else {
            Err(TheoremError::NotImp)
        }
    }
}

#[cfg(test)]
mod test {
    use super::Theorem;
    use crate::pa_convenience::num;
    use crate::pa_formula::{ExprVars, FormulaVars};

    fn x_eq_y() -> FormulaVars {
        ExprVars::var("x").eq(ExprVars::var("y"))
    }

    fn y_eq_x() -> FormulaVars {
        ExprVars::var("y").eq(ExprVars::var("x"))
    }

    fn z_eq_0() -> FormulaVars {
        ExprVars::var("z").eq(ExprVars::z())
    }

    fn one_eq_0() -> FormulaVars {
        num(1).eq(ExprVars::z())
    }

    fn two_eq_0() -> FormulaVars {
        num(2).eq(ExprVars::z())
    }

    #[test]
    fn a1_xy() {
        let t = Theorem::a1(x_eq_y(), y_eq_x(), &["x", "y"]).unwrap();
        let expected: FormulaVars = "@y(@x(x = y -> y = x -> x = y))".parse().unwrap();
        assert_eq!(expected, t.f);
    }

    #[test]
    fn a1_xy_overgen() {
        let t = Theorem::a1(x_eq_y(), y_eq_x(), &["x", "y", "z"]).unwrap();
        let expected: FormulaVars = "@z(@y(@x(x = y -> y = x -> x = y)))".parse().unwrap();
        assert_eq!(expected, t.f);
    }

    #[test]
    fn a1_xx_fails() {
        assert!(Theorem::a1(x_eq_y(), y_eq_x(), &["x", "x"]).is_err());
    }

    #[test]
    fn a1_free_var_fails() {
        assert!(Theorem::a1(x_eq_y(), y_eq_x(), &["x"]).is_err());
    }

    #[test]
    fn a2_xyz() {
        let t = Theorem::a2(x_eq_y(), y_eq_x(), z_eq_0(), &["x", "y", "z"]).unwrap();
        let expected: FormulaVars =
            "@z(@y(@x((x=y -> y=x -> z=0) -> (x=y -> y=x) -> (x=y -> z=0))))"
                .parse()
                .unwrap();
        assert_eq!(expected, t.f);
    }

    #[test]
    fn a3_xy() {
        let t = Theorem::a3(x_eq_y(), &["x", "y"]).unwrap();
        let e: FormulaVars = "@y(@x(!!(x=y) -> x=y))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn a4_xy() {
        let t = Theorem::a4(x_eq_y(), y_eq_x(), "x", &["y"]).unwrap();
        let e: FormulaVars = "@y(@x(x=y -> y=x) -> @x(x=y) -> @x(y=x))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn a4_xx_fail() {
        assert!(Theorem::a4(x_eq_y(), y_eq_x(), "x", &["x"]).is_err());
    }

    #[test]
    fn a4_bound_fail() {
        assert!(Theorem::a4(
            x_eq_y().forall("x").unwrap(),
            y_eq_x().forall("x").unwrap(),
            "x",
            &["y"]
        )
        .is_err());
    }

    #[test]
    fn a5_xz() {
        let t = Theorem::a5(z_eq_0(), "x", &["z"]).unwrap();
        let e: FormulaVars = "@z(z = 0 -> @x(z = 0))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn a5_free_fail() {
        assert!(Theorem::a5(z_eq_0(), "z", &[]).is_err());
    }

    #[test]
    fn a5_bound_fail() {
        assert!(Theorem::a5(z_eq_0().forall("z").unwrap(), "z", &[]).is_err());
    }

    #[test]
    fn a6_xy() {
        let t = Theorem::a6(x_eq_y(), "x", ExprVars::z(), &["y"]).unwrap();
        let e: FormulaVars = "@y(@x(x = y) -> 0 = y)".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn a6_bound_fail() {
        assert!(Theorem::a6(x_eq_y().forall("x").unwrap(), "x", ExprVars::z(), &["y"]).is_err());
    }

    #[test]
    fn mp() {
        let a = Theorem::a1(one_eq_0(), two_eq_0(), &[]).unwrap();
        let b = Theorem::a2(one_eq_0(), two_eq_0(), one_eq_0(), &[]).unwrap();
        let t = b.mp(a).unwrap();
        let e: FormulaVars = "(1=0 -> 2=0) -> (1=0 -> 1=0)".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn mp_not_imp() {
        let a = Theorem::a1(one_eq_0(), two_eq_0(), &[]).unwrap();
        let b = Theorem::a2(one_eq_0(), two_eq_0(), one_eq_0(), &["x"]).unwrap();
        assert!(b.mp(a).is_err());
    }

    #[test]
    fn mp_bad_hyp() {
        let a = Theorem::a1(one_eq_0(), two_eq_0(), &[]).unwrap();
        let b = Theorem::a2(two_eq_0(), two_eq_0(), one_eq_0(), &[]).unwrap();
        assert!(b.mp(a).is_err());
    }
}
