use crate::pa_formula::{Expr, Formula, SyntaxError};

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
    f: Formula,
}

impl From<SyntaxError> for TheoremError {
    fn from(e: SyntaxError) -> Self {
        TheoremError::Syntax(e)
    }
}

impl Expr {
    pub fn free(&self) -> Vec<String> {
        let mut free = vec![];
        self.get_vars_recursive(&[], &[], &mut free).unwrap();  // can only fail if there's bound stuff
        free
    }

    pub fn has_free(&self, x: &str) -> bool {
        self.free().iter().any(|y|y==x)
    }

    fn get_vars_recursive(&self, current_bound: &[String], bound: &[String], free: &mut Vec<String>) -> Result<(), SyntaxError> {
        match self {
            Expr::Z => Ok(()),
            Expr::Var(x) => {
                if !current_bound.contains(x) {
                    if bound.contains(x) {
                        return Err(SyntaxError::MixingFreeAndBound(x.clone()));
                    }
                    if !free.contains(x) {
                        free.push(x.clone());
                    }
                }
                Ok(())
            }
            Expr::S(a) => a.get_vars_recursive(current_bound, bound, free),
            Expr::Add(a,b) | Expr::Mul(a, b) => {
                a.get_vars_recursive(current_bound, bound, free)?;
                b.get_vars_recursive(current_bound, bound, free)
            }
        }
    }
}

impl Formula {
    fn get_vars_recursive(&self, current_bound: &mut Vec<String>, bound: &mut Vec<String>, free: &mut Vec<String>) -> Result<(), SyntaxError> {
        match self {
            Formula::False => Ok(()),
            Formula::Eq(a,b) => {
                a.get_vars_recursive(current_bound, bound, free)?;
                b.get_vars_recursive(current_bound, bound, free)
            }
            Formula::Imp(a,b) => {
                a.get_vars_recursive(current_bound, bound, free)?;
                b.get_vars_recursive(current_bound, bound, free)
            }
            Formula::ForAll(x,a) => {
                if current_bound.contains(x) {
                    return Err(SyntaxError::BoundTwice(x.clone()));
                }
                if free.contains(x) {
                    return Err(SyntaxError::MixingFreeAndBound(x.clone()));
                }
                if !bound.contains(x) {
                    bound.push(x.clone());
                }
                current_bound.push(x.clone());
                let res = a.get_vars_recursive(current_bound, bound, free);
                current_bound.pop();
                res
            }
            Formula::Memo(fv) => {
                for x in fv.bound() {
                    if current_bound.contains(x) {
                        return Err(SyntaxError::BoundTwice(x.clone()));
                    }
                    if free.contains(x) {
                        return Err(SyntaxError::MixingFreeAndBound(x.clone()));
                    }
                    if !bound.contains(x) {
                        bound.push(x.clone());
                    }
                }
                for x in fv.free() {
                    if !current_bound.contains(x) {
                        if bound.contains(x) {
                            return Err(SyntaxError::MixingFreeAndBound(x.clone()));
                        }
                        if !free.contains(x) {
                            free.push(x.clone());
                        }
                    }
                }
                Ok(())
            }
        }
    }

    pub fn check_vars(&self) -> Result<(Vec<String>, Vec<String>), SyntaxError> {
        let mut current_bound = vec![];
        let mut bound = vec![];
        let mut free = vec![];
        self.get_vars_recursive(&mut current_bound, &mut bound, &mut free)?;
        Ok((bound, free))
    }

    pub fn sane(&self) -> Result<(), SyntaxError> {
        self.check_vars()?;
        Ok(())
    }

    pub fn bound(&self) -> Result<Vec<String>, SyntaxError> {
        Ok(self.check_vars()?.0)
    }

    pub fn has_bound(&self, x: &str) -> Result<bool, SyntaxError> {
        Ok(self.bound()?.iter().any(|y|y==x))
    }

    pub fn free(&self) -> Result<Vec<String>, SyntaxError> {
        Ok(self.check_vars()?.1)
    }

    pub fn has_free(&self, x: &str) -> Result<bool, SyntaxError> {
        Ok(self.free()?.iter().any(|y|y==x))
    }

    fn generalize(mut self, gen: &[String]) -> Result<Self, TheoremError> {
        for var in gen.iter().rev() {
            self = self.forall(var);
        }
        if let Some(x) = self.free()?.get(0) {
            Err(TheoremError::FreeVar(x.clone()))
        } else {
            Ok(self)
        }
    }
}

// FOL Axioms and memoing
impl Theorem {
    pub fn formula(&self) -> &Formula {
        &self.f
    }

    pub fn a1(a: Formula, b: Formula, gen: &[String]) -> Result<Self, TheoremError> {
        a.sane()?;
        b.sane()?;
        let f = a.clone().imp(b.imp(a)).generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn a2(
        a: Formula,
        b: Formula,
        c: Formula,
        gen: &[String],
    ) -> Result<Self, TheoremError> {
        a.sane()?;
        b.sane()?;
        c.sane()?;
        let abc = a.clone().imp(b.clone().imp(c.clone()));
        let abac = a.clone().imp(b).imp(a.imp(c));
        let f = abc.imp(abac).generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn a3(a: Formula, gen: &[String]) -> Result<Self, TheoremError> {
        a.sane()?;
        let f = a
            .clone()
            .imp(Formula::falsehood())
            .imp(Formula::falsehood())
            .imp(a)
            .generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn a4(
        a: Formula,
        b: Formula,
        x: &str,
        gen: &[String],
    ) -> Result<Self, TheoremError> {
        if a.has_bound(x)? || b.has_bound(x)? {
            return Err(TheoremError::BoundTwice(x.to_owned()));
        }
        let f = a.clone().imp(b.clone())
            .forall(x)
            .imp(a.forall(x).imp(b.forall(x)))
            .generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn a5(a: Formula, x: &str, gen: &[String]) -> Result<Self, TheoremError> {
        if a.has_free(x)? {
            return Err(TheoremError::MixingFreeAndBound(x.to_owned()));
        }
        if a.has_bound(x)? {
            return Err(TheoremError::BoundTwice(x.to_owned()));
        }
        let f = a.clone().imp(a.forall(x)).generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn a6(a: Formula, x: &str, e: Expr, gen: &[String]) -> Result<Self, TheoremError> {
        let a_bound = a.bound()?;
        for y in e.free() {
            if a_bound.contains(&y) {
                return Err(TheoremError::SubstForBoundVar(y.clone()));
            }
        }
        if a_bound.iter().any(|y|y==x) {
            return Err(TheoremError::SubstBoundVar(x.to_owned()));
        }
        let f = a.clone().forall(x).imp(a.subst(x, &e)?).generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn memo(a: Formula, gen: &[String]) -> Result<Self, TheoremError> {
        a.sane()?;
        let f = a.clone().imp(a.memo()?).generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn unmemo(a: Formula, gen: &[String]) -> Result<Self, TheoremError> {
        a.sane()?;
        let f = a.clone().memo()?.imp(a).generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn mp(self, other: Theorem) -> Result<Self, TheoremError> {
        if let Formula::Imp(a, b) = &self.f {
            if **a == other.f {
                let f = (**b).clone();
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
        let f = Expr::var("x")
            .eq(Expr::var("x"))
            .forall("x");
        Theorem { f }
    }

    pub fn ae2() -> Theorem {
        let f = Expr::var("x")
            .eq(Expr::var("y"))
            .imp(Expr::var("y").eq(Expr::var("x")))
            .forall("y")
            .forall("x");
        Theorem { f }
    }

    pub fn ae3() -> Theorem {
        let f = Expr::var("x")
            .eq(Expr::var("y"))
            .imp(
                Expr::var("y")
                    .eq(Expr::var("z"))
                    .imp(Expr::var("x").eq(Expr::var("z")))
            )
            .forall("z")
            .forall("y")
            .forall("x");
        Theorem { f }
    }

    pub fn aes() -> Theorem {
        let f = Expr::var("x")
            .eq(Expr::var("y"))
            .imp(Expr::var("x").s().eq(Expr::var("y").s()))
            .forall("y")
            .forall("x");
        Theorem { f }
    }

    pub fn aea1() -> Theorem {
        let f = Expr::var("x")
            .eq(Expr::var("y"))
            .imp(
                Expr::var("x")
                    .add(Expr::var("z"))
                    .eq(Expr::var("y").add(Expr::var("z"))),
            )
            .forall("z")
            .forall("y")
            .forall("x");
        Theorem { f }
    }

    pub fn aea2() -> Theorem {
        let f = Expr::var("y")
            .eq(Expr::var("z"))
            .imp(
                Expr::var("x")
                    .add(Expr::var("y"))
                    .eq(Expr::var("x").add(Expr::var("z"))),
            )
            .forall("z")
            .forall("y")
            .forall("x");
        Theorem { f }
    }

    pub fn aem1() -> Theorem {
        let f = Expr::var("x")
            .eq(Expr::var("y"))
            .imp(
                Expr::var("x")
                    .mul(Expr::var("z"))
                    .eq(Expr::var("y").mul(Expr::var("z"))),
            )
            .forall("z")
            .forall("y")
            .forall("x");
        Theorem { f }
    }

    pub fn aem2() -> Theorem {
        let f = Expr::var("y")
            .eq(Expr::var("z"))
            .imp(
                Expr::var("x")
                    .mul(Expr::var("y"))
                    .eq(Expr::var("x").mul(Expr::var("z"))),
            )
            .forall("z")
            .forall("y")
            .forall("x");
        Theorem { f }
    }

    pub fn as1() -> Theorem {
        let f = Expr::z()
            .eq(Expr::var("x").s())
            .imp(Formula::falsehood())
            .forall("x");
        Theorem { f }
    }

    pub fn as2() -> Theorem {
        let f = Expr::var("x")
            .s()
            .eq(Expr::var("y").s())
            .imp(Expr::var("x").eq(Expr::var("y")))
            .forall("y")
            .forall("x");
        Theorem { f }
    }

    pub fn aa1() -> Theorem {
        let f = Expr::var("x")
            .add(Expr::z())
            .eq(Expr::var("x"))
            .forall("x");
        Theorem { f }
    }

    pub fn aa2() -> Theorem {
        let f = Expr::var("x")
            .add(Expr::var("y").s())
            .eq(Expr::var("x").add(Expr::var("y")).s())
            .forall("y")
            .forall("x");
        Theorem { f }
    }

    pub fn am1() -> Theorem {
        let f = Expr::var("x")
            .mul(Expr::z())
            .eq(Expr::z())
            .forall("x");
        Theorem { f }
    }

    pub fn am2() -> Theorem {
        let f = Expr::var("x")
            .mul(Expr::var("y").s())
            .eq(Expr::var("x")
                .mul(Expr::var("y"))
                .add(Expr::var("x")))
            .forall("y")
            .forall("x");
        Theorem { f }
    }

    pub fn aind(a: Formula, x: &str, gen: &[String]) -> Result<Theorem, TheoremError> {
        a.sane()?;
        if a.has_bound(x)? {
            return Err(TheoremError::BoundTwice(x.to_owned()));
        }
        let a0 = a.clone().subst(x, &Expr::z())?;
        let ax = a.clone();
        let asx = a.clone().subst(x, &Expr::var(x).s())?;
        let f = a0
            .imp(ax.imp(asx).forall(x).imp(a.forall(x)))
            .generalize(gen)?;
        Ok(Theorem { f })
    }
}

#[cfg(test)]
mod test {
    use super::Theorem;
    use crate::pa_convenience::num;
    use crate::pa_formula::{Expr, Formula};

    fn v(xs: &[&str]) -> Vec<String> {
        xs.iter().map(|x| (*x).to_owned()).collect()
    }

    fn x_eq_y() -> Formula {
        Expr::var("x").eq(Expr::var("y"))
    }

    fn y_eq_x() -> Formula {
        Expr::var("y").eq(Expr::var("x"))
    }

    fn z_eq_0() -> Formula {
        Expr::var("z").eq(Expr::z())
    }

    fn one_eq_0() -> Formula {
        num(1).eq(Expr::z())
    }

    fn two_eq_0() -> Formula {
        num(2).eq(Expr::z())
    }

    #[test]
    fn a1_xy() {
        let t = Theorem::a1(x_eq_y(), y_eq_x(), &v(&["y", "x"])).unwrap();
        let expected: Formula = "@y(@x(x = y -> y = x -> x = y))".parse().unwrap();
        assert_eq!(expected, t.f);
    }

    #[test]
    fn a1_xy_overgen() {
        let t = Theorem::a1(x_eq_y(), y_eq_x(), &v(&["z", "y", "x"])).unwrap();
        let expected: Formula = "@z(@y(@x(x = y -> y = x -> x = y)))".parse().unwrap();
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
        let t = Theorem::a2(x_eq_y(), y_eq_x(), z_eq_0(), &v(&["z", "y", "x"])).unwrap();
        let expected: Formula =
            "@z(@y(@x((x=y -> y=x -> z=0) -> (x=y -> y=x) -> (x=y -> z=0))))"
                .parse()
                .unwrap();
        assert_eq!(expected, t.f);
    }

    #[test]
    fn a3_xy() {
        let t = Theorem::a3(x_eq_y(), &v(&["y", "x"])).unwrap();
        let e: Formula = "@y(@x(!!(x=y) -> x=y))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn a4_xy() {
        let t = Theorem::a4(x_eq_y(), y_eq_x(), "x", &v(&["y"])).unwrap();
        let e: Formula = "@y(@x(x=y -> y=x) -> @x(x=y) -> @x(y=x))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn a4_xx_fail() {
        assert!(Theorem::a4(x_eq_y(), y_eq_x(), "x", &v(&["x"])).is_err());
    }

    #[test]
    fn a4_bound_fail() {
        assert!(Theorem::a4(
            x_eq_y().forall("x"),
            y_eq_x().forall("x"),
            "x",
            &v(&["y"])
        )
        .is_err());
    }

    #[test]
    fn a5_xz() {
        let t = Theorem::a5(z_eq_0(), "x", &v(&["z"])).unwrap();
        let e: Formula = "@z(z = 0 -> @x(z = 0))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn a5_free_fail() {
        assert!(Theorem::a5(z_eq_0(), "z", &[]).is_err());
    }

    #[test]
    fn a5_bound_fail() {
        assert!(Theorem::a5(z_eq_0().forall("z"), "z", &[]).is_err());
    }

    #[test]
    fn a6_xy() {
        let t = Theorem::a6(x_eq_y(), "x", Expr::z(), &v(&["y"])).unwrap();
        let e: Formula = "@y(@x(x = y) -> 0 = y)".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn a6_bound_fail() {
        assert!(Theorem::a6(
            x_eq_y().forall("x"),
            "x",
            Expr::z(),
            &v(&["y"])
        )
        .is_err());
    }

    #[test]
    fn a6_for_bound_fail() {
        assert!(Theorem::a6(
            x_eq_y().forall("x"),
            "y",
            Expr::var("x").s(),
            &[]
        )
        .is_err());
    }

    #[test]
    fn mp() {
        let a = Theorem::a1(one_eq_0(), two_eq_0(), &[]).unwrap();
        let b = Theorem::a2(one_eq_0(), two_eq_0(), one_eq_0(), &[]).unwrap();
        let t = b.mp(a).unwrap();
        let e: Formula = "(1=0 -> 2=0) -> (1=0 -> 1=0)".parse().unwrap();
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
        let e: Formula = "@x(x = x)".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn ae2() {
        let t = Theorem::ae2();
        let e: Formula = "@x(@y(x = y -> y = x))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn ae3() {
        let t = Theorem::ae3();
        let e: Formula = "@x(@y(@z(x = y -> y = z -> x = z)))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn aes() {
        let t = Theorem::aes();
        let e: Formula = "@x(@y(x = y -> S(x) = S(y)))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn aea1() {
        let t = Theorem::aea1();
        let e: Formula = "@x(@y(@z(x = y -> x + z = y + z)))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn aea2() {
        let t = Theorem::aea2();
        let e: Formula = "@x(@y(@z(y = z -> x + y = x + z)))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn aem1() {
        let t = Theorem::aem1();
        let e: Formula = "@x(@y(@z(x = y -> x * z = y * z)))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn aem2() {
        let t = Theorem::aem2();
        let e: Formula = "@x(@y(@z(y = z -> x * y = x * z)))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn as1() {
        let t = Theorem::as1();
        let e: Formula = "@x(!(0 = S(x)))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn as2() {
        let t = Theorem::as2();
        let e: Formula = "@x(@y(S(x) = S(y) -> x = y))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn aa1() {
        let t = Theorem::aa1();
        let e: Formula = "@x(x + 0 = x)".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn aa2() {
        let t = Theorem::aa2();
        let e: Formula = "@x(@y(x + S(y) = S(x + y)))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn am1() {
        let t = Theorem::am1();
        let e: Formula = "@x(x * 0 = 0)".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn am2() {
        let t = Theorem::am2();
        let e: Formula = "@x(@y(x * S(y) = x * y + x))".parse().unwrap();
        assert_eq!(e, t.f);
    }

    #[test]
    fn aind_xy() {
        let t = Theorem::aind(x_eq_y(), "x", &v(&["y"])).unwrap();
        let e: Formula = "@y(0=y -> @x(x = y -> S(x) = y) -> @x(x = y))"
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
        assert!(Theorem::aind(z_eq_0().forall("z"), "z", &[]).is_err());
    }
}
