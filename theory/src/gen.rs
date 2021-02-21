use kernel::pa_axiom::{Theorem,TheoremError};
use kernel::pa_formula::{ExprVars,Formula,FormulaVars,SyntaxError};
use kernel::pa_parse::ParseError;

#[derive(Debug)]
pub enum TheoryError {
    Syntax(SyntaxError),
    Axiom(TheoremError),
    Parse(ParseError),
    CheckMismatch(String),
    NotAbsentGen(String),
    NotForAll,
    NotImp,
    NotOuterVar(String),
    RenameInnerConflict(String),
    RenameOuterConflict(String),
    SubstNotInEnvironment(String),
    SubstOuterConflict(String),
    VarMismatch(String,String),
    WrongHyp,
}

impl From<SyntaxError> for TheoryError {
    fn from(e: SyntaxError) -> Self {
        TheoryError::Syntax(e)
    }
}

impl From<TheoremError> for TheoryError {
    fn from(e: TheoremError) -> Self {
        TheoryError::Axiom(e)
    }
}

impl From<ParseError> for TheoryError {
    fn from(e: ParseError) -> Self {
        TheoryError::Parse(e)
    }
}

pub trait TheoremGen : Sized {
    fn absent_gen(self, gen: &[String]) -> Result<Self, TheoryError>;
    fn check(self, parseable: &str) -> Result<Self, TheoryError>;
    fn gen_mp(self, other: Self, count: usize) -> Result<Self, TheoryError>;
    fn outer_rename(self, x: &str, y: &str) -> Result<Self, TheoryError>;
    fn subst_gen(self, es: &[ExprVars], gen: &[String]) -> Result<Self, TheoryError>;
    fn subst_one(self, x: &str, e: ExprVars) -> Result<Self, TheoryError>;
}

fn peel_forall(a: &FormulaVars) -> Result<(String, FormulaVars), TheoryError> {
    if let Formula::ForAll(x,f) = a.formula() {
        Ok((x.to_owned(), f.reconstitute()?))
    } else {
        Err(TheoryError::NotForAll)
    }
}

fn peel_foralls(a: &FormulaVars, count: usize) -> Result<(Vec<String>, FormulaVars), TheoryError> {
    let mut vars = vec![];
    let mut f = a.formula();
    for _ in 0..count {
        if let Formula::ForAll(x,f2) = f {
            vars.push(x.to_owned());
            f = f2;
        } else {
            return Err(TheoryError::NotForAll);
        }
    }
    vars.reverse();
    Ok((vars, f.reconstitute()?))
}

fn peel_foralls_until(a: &FormulaVars, x: &str) -> Result<(Vec<String>, FormulaVars), TheoryError> {
    let mut vars = vec![];
    let mut f = a.formula();
    loop {
        if let Formula::ForAll(y,f2) = f {
            if y == x {
                break;
            } else {
                f = f2;
                vars.push(y.to_owned());
            }
        } else {
            return Err(TheoryError::NotOuterVar(x.to_owned()));
        }
    }
    vars.reverse();
    Ok((vars, f.reconstitute()?))
}

fn check_expr_environment(e: &ExprVars, vars: &[String]) -> Result<(), TheoryError> {
    for x in e.free() {
        if !vars.contains(x) {
            return Err(TheoryError::SubstNotInEnvironment(x.clone()));
        }
    }
    Ok(())
}

impl TheoremGen for Theorem {
    fn check(self, parseable: &str) -> Result<Self, TheoryError> {
        if parseable.parse::<FormulaVars>()? == *self.formula() {
            Ok(self)
        } else {
            Err(TheoryError::CheckMismatch(parseable.to_owned()))
        }
    }

    fn outer_rename(self, x: &str, y: &str) -> Result<Self, TheoryError> {
        if x == y {
            return Ok(self);
        }

        let (mut vars, xf) = peel_foralls_until(self.formula(), x)?;
        let (_, f) = peel_forall(&xf)?;
        
        if vars.iter().any(|y|y==x) {
            return Err(TheoryError::RenameOuterConflict(x.to_owned()));
        }
        if f.has_bound(x) {
            return Err(TheoryError::RenameInnerConflict(x.to_owned()));
        }

        // self: @v...@x(f[x])
        let t1 = Theorem::a5(xf, y, &vars)?.gen_mp(self, vars.len())?;   // @v...@y(@x(f[x]))

        vars.insert(0, y.to_owned());
        let t2 = Theorem::a6(f, x, ExprVars::var(y), &vars)?;
        Ok(t2.gen_mp(t1, vars.len())?)    // @v...@y(f[y])
    }

    fn subst_one(self, x: &str, e: ExprVars) -> Result<Self, TheoryError> {
        let (vars, xf) = peel_foralls_until(self.formula(), x)?;
        let (_, f) = peel_forall(&xf)?;

        //check_expr_environment(&e, &vars)?;

        if vars.iter().any(|y|y==x) {
            return Err(TheoryError::SubstOuterConflict(x.to_owned()));
        }

        // self: @v...@x(f[x])
        let t1 = Theorem::a6(f, x, e, &vars)?;    // @v...(@x(f[x]) -> f[e])
        println!("{:?}", t1);
        Ok(t1.gen_mp(self, vars.len())?)
    }

    fn absent_gen(mut self, gen: &[String]) -> Result<Self, TheoryError> {
        for x in gen {
            if self.formula().has_bound(x) {
                return Err(TheoryError::NotAbsentGen(x.clone()));
            }
            self = Theorem::a5(self.formula().clone(), x, &[])?.mp(self)?;
        }
        Ok(self)
    }

    fn subst_gen(self, es: &[ExprVars], gen: &[String]) -> Result<Self, TheoryError> {
        let (vars,f) = peel_foralls(self.formula(), gen.len())?;
        // self @v...@x(f[x])
        panic!();
    }

    fn gen_mp(self, other: Self, count: usize) -> Result<Self, TheoryError> {
        if count == 0 {
            Ok(self.mp(other)?)
        } else {
            let (xs, xa) = peel_foralls(self.formula(), count-1)?;
            let (ys, yb) = peel_foralls(other.formula(), count-1)?;
            for i in 0..count-1 {
                if xs[i] != ys[i] {
                    return Err(TheoryError::VarMismatch(xs[i].clone(), ys[i].clone()));
                }
            }
            let (x, ab) = peel_forall(&xa)?;
            let (y, a) = peel_forall(&yb)?;
            if x != y {
                return Err(TheoryError::VarMismatch(x.clone(), y.clone()));
            }
            let b = match ab.formula() {
                Formula::Imp(h,af) => {
                    if **h != *a.formula() {
                        return Err(TheoryError::WrongHyp);
                    }
                    af.reconstitute()?
                }
                _ => return Err(TheoryError::NotImp)
            };
            // self: @xs...@x(a->b)
            // other: @xs...@x(a)
            let t = Theorem::a4(a, b, &x, &xs)?;   // @xs...(@x(a->b)->(@x(a)->@x(b)))
            let t1 = t.gen_mp(self, count-1)?;
            let t2 = t1.gen_mp(other, count-1)?;
            Ok(t2)
        }
    }
}

#[cfg(test)]
mod test {
    use kernel::pa_axiom::Theorem;
    use kernel::pa_formula::{FormulaVars};
    use kernel::pa_convenience::num;
    use super::TheoremGen;

    #[test]
    fn outer_rename_same() {
        let t = Theorem::aa2();  // @x(@y(x + S(y) = S(x + y)))
        let t1 = t.outer_rename("x", "x").unwrap();
        let e:FormulaVars = "@x(@y(x + S(y) = S(x + y)))".parse().unwrap();
        assert_eq!(e, *t1.formula());
    }

    #[test]
    fn outer_rename_1() {
        let t = Theorem::aa2();  // @x(@y(x + S(y) = S(x + y)))
        let t1 = t.outer_rename("x", "x1").unwrap();
        let e:FormulaVars = "@x1(@y(x1 + S(y) = S(x1 + y)))".parse().unwrap();
        assert_eq!(e, *t1.formula());
    }

    #[test]
    fn outer_rename_2() {
        let t = Theorem::aa2();  // @x(@y(x + S(y) = S(x + y)))
        let t1 = t.outer_rename("y", "y1").unwrap();
        let e:FormulaVars = "@x(@y1(x + S(y1) = S(x + y1)))".parse().unwrap();
        assert_eq!(e, *t1.formula());
    }

    #[test]
    fn outer_rename_3() {
        let t = Theorem::aea1(); // @x(@y(@z(x = y -> x + z = y + z)))
        let t1 = t.outer_rename("z", "w").unwrap();
        let e: FormulaVars = "@x(@y(@w(x = y -> x + w = y + w)))".parse().unwrap();
        assert_eq!(e, *t1.formula());
    }

    #[test]
    fn outer_rename_outer_conflict() {
        let t = Theorem::aea1(); // @x(@y(@z(x = y -> x + z = y + z)))
        assert!(t.outer_rename("y", "x").is_err());
    }

    #[test]
    fn outer_rename_outer_inner() {
        let t = Theorem::aea1(); // @x(@y(@z(x = y -> x + z = y + z)))
        assert!(t.outer_rename("y", "z").is_err());
    }

    #[test]
    fn absent_gen_none() {
        let t = Theorem::aa1().check("@x(x + 0 = x)").unwrap();
        let t1 = t.absent_gen(&[]).unwrap();
        t1.check("@x(x + 0 = x)").unwrap();
    }

    fn v(xs: &[&str]) -> Vec<String> {
        xs.iter().map(|x|(*x).to_owned()).collect()
    }

    #[test]
    fn absent_gen_one() {
        let t = Theorem::aa1().check("@x(x + 0 = x)").unwrap();
        let t1 = t.absent_gen(&v(&["y"])).unwrap();
        t1.check("@y(@x(x + 0 = x))").unwrap();
    }

    #[test]
    fn absent_gen_three() {
        let t = Theorem::aa1().check("@x(x + 0 = x)").unwrap();
        let t1 = t.absent_gen(&v(&["y","z","w"])).unwrap();
        t1.check("@w(@z(@y(@x(x + 0 = x))))").unwrap();
    }

    #[test]
    fn absent_gen_same_fail() {
        let t = Theorem::aa1().check("@x(x + 0 = x)").unwrap();
        assert!(t.absent_gen(&v(&["x"])).is_err());
    }

    #[test]
    fn subst_one_const() {
        let t = Theorem::aa1().check("@x(x + 0 = x)").unwrap();
        let t1 = t.subst_one("x", num(0)).unwrap();
        t1.check("0 + 0 = 0").unwrap();
    }

    #[test]
    fn subst_one_var1_err() {
        let t = Theorem::aa2().check("@x(@y(x + S(y) = S(x + y)))").unwrap();
        assert!(t.subst_one("x", "S(y)".parse().unwrap()).is_err());
    }

    #[test]
    fn subst_one_varz_err() {
        let t = Theorem::aa2().check("@x(@y(x + S(y) = S(x + y)))").unwrap();
        assert!(t.subst_one("x", "S(z)".parse().unwrap()).is_err());
    }

    #[test]
    fn subst_one_var2() {
        let t = Theorem::aa2().check("@x(@y(x + S(y) = S(x + y)))").unwrap();
        let t1 = t.subst_one("y", "S(x)".parse().unwrap()).unwrap();
        t1.check("@x(x + S(S(x)) = S(x + S(x)))").unwrap();
    }
}
