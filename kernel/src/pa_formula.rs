use std::rc::Rc;

#[derive(Debug)]
pub enum SyntaxError {
    MixingFreeAndBound(String),
    BoundTwice(String),
    SubstBoundVar(String),
    SubstForBoundVar(String),
}

#[derive(Clone, Eq, PartialEq)]
pub enum Expr {
    Var(String),
    Z,
    S(Rc<Expr>),
    Add(Rc<Expr>, Rc<Expr>),
    Mul(Rc<Expr>, Rc<Expr>),
}

impl std::fmt::Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Expr::Var(x) => write!(f, "{}", x),
            Expr::Z => write!(f, "0"),
            Expr::S(e) => write!(f, "S({:?})", e),
            Expr::Add(a, b) => write!(f, "({:?}+{:?})", a, b),
            Expr::Mul(a, b) => write!(f, "({:?}+{:?})", a, b),
        }
    }
}

#[derive(Clone, Eq, PartialEq)]
pub enum Formula {
    False,
    Eq(Rc<Expr>, Rc<Expr>),
    Imp(Rc<Formula>, Rc<Formula>),
    ForAll(String, Rc<Formula>),
    Memo(FormulaVars),
}

impl std::fmt::Debug for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Formula::False => write!(f, "false"),
            Formula::Eq(a, b) => write!(f, "({:?}={:?})", a, b),
            Formula::Imp(a, b) => write!(f, "({:?} -> {:?})", a, b),
            Formula::ForAll(x, a) => write!(f, "@{}({:?})", x, a),
            Formula::Memo(fv) => write!(f, "{:?}", fv),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExprVars {
    e: Rc<Expr>,
    free: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FormulaVars {
    f: Rc<Formula>,
    free: Vec<String>,
    bound: Vec<String>,
}

impl Expr {
    pub fn var(x: &str) -> Self {
        Expr::Var(x.to_owned())
    }

    pub fn z() -> Self {
        Expr::Z
    }

    pub fn s(self) -> Self {
        Expr::S(Rc::new(self))
    }

    pub fn add(self, other: Self) -> Self {
        Expr::Add(Rc::new(self), Rc::new(other))
    }

    pub fn mul(self, other: Self) -> Self {
        Expr::Mul(Rc::new(self), Rc::new(other))
    }

    pub fn eq(self, other: Self) -> Formula {
        Formula::Eq(Rc::new(self), Rc::new(other))
    }

    pub fn reconstitute(&self) -> ExprVars {
        ExprVars {
            e: Rc::new(self.clone()),
            free: self.free(),
        }
    }
}

impl ExprVars {
    pub fn expr(&self) -> &Expr {
        &self.e
    }

    pub fn free(&self) -> &[String] {
        &self.free
    }
}

impl Formula {
    pub fn reconstitute(&self) -> Result<FormulaVars, SyntaxError> {
        let (bound, free) = self.check_vars()?;
        Ok(FormulaVars {
            f: Rc::new(self.clone()),
            bound,
            free
        })
    }

    pub fn falsehood() -> Self {
        Formula::False
    }

    pub fn imp(self, other: Self) -> Self {
        Formula::Imp(Rc::new(self), Rc::new(other))
    }

    pub fn forall(self, x: &str) -> Self {
        Formula::ForAll(x.to_owned(), Rc::new(self))
    }

    pub fn memo(self) -> Result<Self, SyntaxError> {
        Ok(Formula::Memo(self.reconstitute()?))
    }
}

impl FormulaVars {
    pub fn formula(&self) -> &Formula {
        &self.f
    }

    pub fn free(&self) -> &[String] {
        &self.free
    }

    pub fn bound(&self) -> &[String] {
        &self.bound
    }
}
