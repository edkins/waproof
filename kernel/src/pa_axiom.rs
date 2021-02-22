use crate::pa_formula::{ExprVars, Formula, FormulaVars, SyntaxError};

#[derive(Debug)]
pub enum TheoremError {
    Syntax(SyntaxError),
    FreeVar(String),
    MixingFreeAndBound(String),
    BoundTwice(String),
    SubstBoundVar(String),
    SubstForBoundVar(String),
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
    fn generalize(mut self, gen: &[String]) -> Result<Self, TheoremError> {
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

// FOL Axioms and memoing
impl Theorem {
    pub fn formula(&self) -> &FormulaVars {
        &self.f
    }

    pub fn a1(a: FormulaVars, b: FormulaVars, gen: &[String]) -> Result<Self, TheoremError> {
        let f = a.clone().imp(b.imp(a)?)?.generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn a2(
        a: FormulaVars,
        b: FormulaVars,
        c: FormulaVars,
        gen: &[String],
    ) -> Result<Self, TheoremError> {
        let abc = a.clone().imp(b.clone().imp(c.clone())?)?;
        let abac = a.clone().imp(b)?.imp(a.imp(c)?)?;
        let f = abc.imp(abac)?.generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn a3(a: FormulaVars, gen: &[String]) -> Result<Self, TheoremError> {
        let f = a
            .clone()
            .imp(FormulaVars::falsehood())?
            .imp(FormulaVars::falsehood())?
            .imp(a)?
            .generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn a4(
        a: FormulaVars,
        b: FormulaVars,
        x: &str,
        gen: &[String],
    ) -> Result<Self, TheoremError> {
        if a.has_bound(x) || b.has_bound(x) {
            return Err(TheoremError::BoundTwice(x.to_owned()));
        }
        let f = (a.clone().imp(b.clone())?)
            .forall(x)?
            .imp(a.forall(x)?.imp(b.forall(x)?)?)?
            .generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn a5(a: FormulaVars, x: &str, gen: &[String]) -> Result<Self, TheoremError> {
        if a.has_free(x) {
            return Err(TheoremError::MixingFreeAndBound(x.to_owned()));
        }
        if a.has_bound(x) {
            return Err(TheoremError::BoundTwice(x.to_owned()));
        }
        let f = a.clone().imp(a.forall(x)?)?.generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn a6(a: FormulaVars, x: &str, e: ExprVars, gen: &[String]) -> Result<Self, TheoremError> {
        for y in e.free() {
            if a.has_bound(y) {
                return Err(TheoremError::SubstForBoundVar(y.clone()));
            }
        }
        if a.has_bound(x) {
            return Err(TheoremError::SubstBoundVar(x.to_owned()));
        }
        let f = a.clone().forall(x)?.imp(a.subst(x, &e)?)?.generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn memo(a: FormulaVars, gen: &[String]) -> Result<Self, TheoremError> {
        let f = a.clone().imp(a.memo())?.generalize(gen)?;
        Ok(Theorem { f })
    }
    
    pub fn unmemo(a: FormulaVars, gen: &[String]) -> Result<Self, TheoremError> {
        let f = a.clone().memo().imp(a)?.generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn mp(self, other: Theorem) -> Result<Self, TheoremError> {
        if let Formula::Imp(a, b) = self.f.formula() {
            if **a == *other.f.formula() {
                let f = b.reconstitute()?;
                Ok(Theorem { f })
            } else {
                //panic!();   // helps if you want a stack trace
                Err(TheoremError::WrongHyp)
            }
        } else {
            Err(TheoremError::NotImp)
        }
    }
}

// PA Axioms
impl Theorem {
    pub fn ae1() -> Theorem {
        let f = ExprVars::var("x")
            .eq(ExprVars::var("x"))
            .forall("x")
            .unwrap();
        Theorem { f }
    }

    pub fn ae2() -> Theorem {
        let f = ExprVars::var("x")
            .eq(ExprVars::var("y"))
            .imp(ExprVars::var("y").eq(ExprVars::var("x")))
            .unwrap()
            .forall("y")
            .unwrap()
            .forall("x")
            .unwrap();
        Theorem { f }
    }

    pub fn ae3() -> Theorem {
        let f = ExprVars::var("x")
            .eq(ExprVars::var("y"))
            .imp(
                ExprVars::var("y")
                    .eq(ExprVars::var("z"))
                    .imp(ExprVars::var("x").eq(ExprVars::var("z")))
                    .unwrap(),
            )
            .unwrap()
            .forall("z")
            .unwrap()
            .forall("y")
            .unwrap()
            .forall("x")
            .unwrap();
        Theorem { f }
    }

    pub fn aes() -> Theorem {
        let f = ExprVars::var("x")
            .eq(ExprVars::var("y"))
            .imp(ExprVars::var("x").s().eq(ExprVars::var("y").s()))
            .unwrap()
            .forall("y")
            .unwrap()
            .forall("x")
            .unwrap();
        Theorem { f }
    }

    pub fn aea1() -> Theorem {
        let f = ExprVars::var("x")
            .eq(ExprVars::var("y"))
            .imp(
                ExprVars::var("x")
                    .add(ExprVars::var("z"))
                    .eq(ExprVars::var("y").add(ExprVars::var("z"))),
            )
            .unwrap()
            .forall("z")
            .unwrap()
            .forall("y")
            .unwrap()
            .forall("x")
            .unwrap();
        Theorem { f }
    }

    pub fn aea2() -> Theorem {
        let f = ExprVars::var("y")
            .eq(ExprVars::var("z"))
            .imp(
                ExprVars::var("x")
                    .add(ExprVars::var("y"))
                    .eq(ExprVars::var("x").add(ExprVars::var("z"))),
            )
            .unwrap()
            .forall("z")
            .unwrap()
            .forall("y")
            .unwrap()
            .forall("x")
            .unwrap();
        Theorem { f }
    }

    pub fn aem1() -> Theorem {
        let f = ExprVars::var("x")
            .eq(ExprVars::var("y"))
            .imp(
                ExprVars::var("x")
                    .mul(ExprVars::var("z"))
                    .eq(ExprVars::var("y").mul(ExprVars::var("z"))),
            )
            .unwrap()
            .forall("z")
            .unwrap()
            .forall("y")
            .unwrap()
            .forall("x")
            .unwrap();
        Theorem { f }
    }

    pub fn aem2() -> Theorem {
        let f = ExprVars::var("y")
            .eq(ExprVars::var("z"))
            .imp(
                ExprVars::var("x")
                    .mul(ExprVars::var("y"))
                    .eq(ExprVars::var("x").mul(ExprVars::var("z"))),
            )
            .unwrap()
            .forall("z")
            .unwrap()
            .forall("y")
            .unwrap()
            .forall("x")
            .unwrap();
        Theorem { f }
    }

    pub fn as1() -> Theorem {
        let f = ExprVars::z()
            .eq(ExprVars::var("x").s())
            .imp(FormulaVars::falsehood())
            .unwrap()
            .forall("x")
            .unwrap();
        Theorem { f }
    }

    pub fn as2() -> Theorem {
        let f = ExprVars::var("x")
            .s()
            .eq(ExprVars::var("y").s())
            .imp(ExprVars::var("x").eq(ExprVars::var("y")))
            .unwrap()
            .forall("y")
            .unwrap()
            .forall("x")
            .unwrap();
        Theorem { f }
    }

    pub fn aa1() -> Theorem {
        let f = ExprVars::var("x")
            .add(ExprVars::z())
            .eq(ExprVars::var("x"))
            .forall("x")
            .unwrap();
        Theorem { f }
    }

    pub fn aa2() -> Theorem {
        let f = ExprVars::var("x")
            .add(ExprVars::var("y").s())
            .eq(ExprVars::var("x").add(ExprVars::var("y")).s())
            .forall("y")
            .unwrap()
            .forall("x")
            .unwrap();
        Theorem { f }
    }

    pub fn am1() -> Theorem {
        let f = ExprVars::var("x")
            .mul(ExprVars::z())
            .eq(ExprVars::z())
            .forall("x")
            .unwrap();
        Theorem { f }
    }

    pub fn am2() -> Theorem {
        let f = ExprVars::var("x")
            .mul(ExprVars::var("y").s())
            .eq(ExprVars::var("x")
                .mul(ExprVars::var("y"))
                .add(ExprVars::var("x")))
            .forall("y")
            .unwrap()
            .forall("x")
            .unwrap();
        Theorem { f }
    }

    pub fn aind(a: FormulaVars, x: &str, gen: &[String]) -> Result<Theorem, TheoremError> {
        if a.has_bound(x) {
            return Err(TheoremError::BoundTwice(x.to_owned()));
        }
        let a0 = a.clone().subst(x, &ExprVars::z())?;
        let ax = a.clone();
        let asx = a.clone().subst(x, &ExprVars::var(x).s())?;
        let f = a0
            .imp(ax.imp(asx)?.forall(x)?.imp(a.forall(x)?)?)?
            .generalize(gen)?;
        Ok(Theorem { f })
    }
}

#[cfg(test)]
mod test {
    use super::Theorem;
    use crate::pa_convenience::num;
    use crate::pa_formula::{ExprVars, FormulaVars};

    fn v(xs: &[&str]) -> Vec<String> {
        xs.iter().map(|x| (*x).to_owned()).collect()
    }

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
        let t = Theorem::a1(x_eq_y(), y_eq_x(), &v(&["x", "y"])).unwrap();
        let expected: FormulaVars = "@y(@x(x = y -> y = x -> x = y))".parse().unwrap();
        assert_eq!(expected, t.f);
    }

    #[test]
    fn a1_xy_overgen() {
        let t = Theorem::a1(x_eq_y(), y_eq_x(), &v(&["x", "y", "z"])).unwrap();
        let expected: FormulaVars = "@z(@y(@x(x = y -> y = x -> x = y)))".parse().unwrap();
        assert_eq!(expected, t.f);
    }

    #[test]
    fn a1_xx_fails() {
        assert!(Theorem::a1(x_eq_y(), y_eq_x(), &v(&["x", "x"])).is_err());
    }

    #[test]
    fn a1_free_var_fails() {
        assert!(Theorem::a1(x_eq_y(), y_eq_x(), &v(&["x"])).is_err());
    }

    #[test]
    fn a2_xyz() {
        let t = Theorem::a2(x_eq_y(), y_eq_x(), z_eq_0(), &v(&["x", "y", "z"])).unwrap();
        let expected: FormulaVars =
            "@z(@y(@x((x=y -> y=x -> z=0) -> (x=y -> y=x) -> (x=y -> z=0))))"
                .parse()
                .unwrap();
        assert_eq!(expected, t.f);
    }

    #[test]
    fn a3_xy() {
        let t = Theorem::a3(x_eq_y(), &v(&["x", "y"])).unwrap();
        let e: FormulaVars = "@y(@x(!!(x=y) -> x=y))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn a4_xy() {
        let t = Theorem::a4(x_eq_y(), y_eq_x(), "x", &v(&["y"])).unwrap();
        let e: FormulaVars = "@y(@x(x=y -> y=x) -> @x(x=y) -> @x(y=x))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn a4_xx_fail() {
        assert!(Theorem::a4(x_eq_y(), y_eq_x(), "x", &v(&["x"])).is_err());
    }

    #[test]
    fn a4_bound_fail() {
        assert!(Theorem::a4(
            x_eq_y().forall("x").unwrap(),
            y_eq_x().forall("x").unwrap(),
            "x",
            &v(&["y"])
        )
        .is_err());
    }

    #[test]
    fn a5_xz() {
        let t = Theorem::a5(z_eq_0(), "x", &v(&["z"])).unwrap();
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
        let t = Theorem::a6(x_eq_y(), "x", ExprVars::z(), &v(&["y"])).unwrap();
        let e: FormulaVars = "@y(@x(x = y) -> 0 = y)".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn a6_bound_fail() {
        assert!(Theorem::a6(
            x_eq_y().forall("x").unwrap(),
            "x",
            ExprVars::z(),
            &v(&["y"])
        )
        .is_err());
    }

    #[test]
    fn a6_for_bound_fail() {
        assert!(Theorem::a6(
            x_eq_y().forall("x").unwrap(),
            "y",
            ExprVars::var("x").s(),
            &[]
        )
        .is_err());
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
        let b = Theorem::a2(one_eq_0(), two_eq_0(), one_eq_0(), &v(&["x"])).unwrap();
        assert!(b.mp(a).is_err());
    }

    #[test]
    fn mp_bad_hyp() {
        let a = Theorem::a1(one_eq_0(), two_eq_0(), &[]).unwrap();
        let b = Theorem::a2(two_eq_0(), two_eq_0(), one_eq_0(), &[]).unwrap();
        assert!(b.mp(a).is_err());
    }

    #[test]
    fn ae1() {
        let t = Theorem::ae1();
        let e: FormulaVars = "@x(x = x)".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn ae2() {
        let t = Theorem::ae2();
        let e: FormulaVars = "@x(@y(x = y -> y = x))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn ae3() {
        let t = Theorem::ae3();
        let e: FormulaVars = "@x(@y(@z(x = y -> y = z -> x = z)))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn aes() {
        let t = Theorem::aes();
        let e: FormulaVars = "@x(@y(x = y -> S(x) = S(y)))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn aea1() {
        let t = Theorem::aea1();
        let e: FormulaVars = "@x(@y(@z(x = y -> x + z = y + z)))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn aea2() {
        let t = Theorem::aea2();
        let e: FormulaVars = "@x(@y(@z(y = z -> x + y = x + z)))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn aem1() {
        let t = Theorem::aem1();
        let e: FormulaVars = "@x(@y(@z(x = y -> x * z = y * z)))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn aem2() {
        let t = Theorem::aem2();
        let e: FormulaVars = "@x(@y(@z(y = z -> x * y = x * z)))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn as1() {
        let t = Theorem::as1();
        let e: FormulaVars = "@x(!(0 = S(x)))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn as2() {
        let t = Theorem::as2();
        let e: FormulaVars = "@x(@y(S(x) = S(y) -> x = y))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn aa1() {
        let t = Theorem::aa1();
        let e: FormulaVars = "@x(x + 0 = x)".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn aa2() {
        let t = Theorem::aa2();
        let e: FormulaVars = "@x(@y(x + S(y) = S(x + y)))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn am1() {
        let t = Theorem::am1();
        let e: FormulaVars = "@x(x * 0 = 0)".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn am2() {
        let t = Theorem::am2();
        let e: FormulaVars = "@x(@y(x * S(y) = x * y + x))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn aind_xy() {
        let t = Theorem::aind(x_eq_y(), "x", &v(&["y"])).unwrap();
        let e: FormulaVars = "@y(0=y -> @x(x = y -> S(x) = y) -> @x(x = y))"
            .parse()
            .unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn aind_zz_fail() {
        assert!(Theorem::aind(z_eq_0(), "z", &v(&["z"])).is_err());
    }

    #[test]
    fn aind_bound_fail() {
        assert!(Theorem::aind(z_eq_0().forall("z").unwrap(), "z", &[]).is_err());
    }
}
