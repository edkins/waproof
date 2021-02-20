use crate::pa_formula::{FormulaVars,SyntaxError};

#[derive(Debug)]
pub enum TheoremError {
    Syntax(SyntaxError),
    FreeVar(String),
}

#[derive(Clone,Debug,Eq,PartialEq)]
pub struct Theorem {
    f: FormulaVars,
}

impl From<SyntaxError> for TheoremError {
    fn from(e: SyntaxError) -> Self {
        TheoremError::Syntax(e)
    }
}

impl FormulaVars {
    fn generalize(mut self, gen: &[&str]) -> Result<Self,TheoremError> {
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

    pub fn a1(a: FormulaVars, b: FormulaVars, gen: &[&str]) -> Result<Self,TheoremError> {
        let f = a.clone().imp(b.imp(a)?)?.generalize(gen)?;
        Ok(Theorem { f })
    }

    pub fn a2(a: FormulaVars, b: FormulaVars, c: FormulaVars, gen: &[&str]) -> Result<Self, TheoremError> {
        let abc = a.clone().imp(b.clone().imp(c.clone())?)?;
        let abac = a.clone().imp(b)?.imp(a.imp(c)?)?;
        let f = abc.imp(abac)?.generalize(gen)?;
        Ok(Theorem{ f })
    }

    pub fn a3(a: FormulaVars, gen: &[&str]) -> Result<Self, TheoremError> {
        let f = a.clone().imp(FormulaVars::falsehood())?.imp(FormulaVars::falsehood())?.imp(a)?.generalize(gen)?;
        Ok(Theorem{ f })
    }
}

#[cfg(test)]
mod test {
    use super::Theorem;
    use crate::pa_formula::{ExprVars,FormulaVars};

    fn x_eq_y() -> FormulaVars {
        ExprVars::var("x").eq(ExprVars::var("y"))
    }

    fn y_eq_x() -> FormulaVars {
        ExprVars::var("y").eq(ExprVars::var("x"))
    }

    fn z_eq_0() -> FormulaVars {
        ExprVars::var("z").eq(ExprVars::z())
    }

    #[test]
    fn a1_xy() {
        let t = Theorem::a1(x_eq_y(), y_eq_x(), &["x","y"]).unwrap();
        let expected:FormulaVars = "@y(@x(x = y -> y = x -> x = y))".parse().unwrap();
        assert_eq!(expected, t.f);
    }

    #[test]
    fn a1_xy_overgen() {
        let t = Theorem::a1(x_eq_y(), y_eq_x(), &["x","y","z"]).unwrap();
        let expected:FormulaVars = "@z(@y(@x(x = y -> y = x -> x = y)))".parse().unwrap();
        assert_eq!(expected, t.f);
    }

    #[test]
    fn a1_xx_fails() {
        assert!(Theorem::a1(x_eq_y(), y_eq_x(), &["x","x"]).is_err());
    }

    #[test]
    fn a1_free_var_fails() {
        assert!(Theorem::a1(x_eq_y(), y_eq_x(), &["x"]).is_err());
    }

    #[test]
    fn a2_xyz() {
        let t = Theorem::a2(x_eq_y(), y_eq_x(), z_eq_0(), &["x","y","z"]).unwrap();
        let expected:FormulaVars = "@z(@y(@x((x=y -> y=x -> z=0) -> (x=y -> y=x) -> (x=y -> z=0))))".parse().unwrap();
        assert_eq!(expected, t.f);
    }

    #[test]
    fn a3_xy() {
        let t = Theorem::a3(x_eq_y(), &["x","y"]).unwrap();
        let e:FormulaVars = "@y(@x(!!(x=y) -> x=y))".parse().unwrap();
        assert_eq!(e, t.f);
    }
}
