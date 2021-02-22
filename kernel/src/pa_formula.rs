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

fn merge_lists(mut a: Vec<String>, mut b: Vec<String>) -> Vec<String> {
    for x in b.drain(..) {
        if !a.contains(&x) {
            a.push(x);
        }
    }
    a
}

fn list_remove(mut a: Vec<String>, x: &str) -> Vec<String> {
    a.drain(..).filter(|y| y != x).collect()
}

fn list_intersect(a: &[String], b: &[String]) -> Option<String> {
    for x in a {
        if b.contains(x) {
            return Some(x.clone());
        }
    }
    None
}

impl ExprVars {
    pub fn expr(&self) -> &Expr {
        &self.e
    }

    pub fn free(&self) -> &[String] {
        &self.free
    }

    pub fn var(x: &str) -> Self {
        ExprVars {
            e: Rc::new(Expr::Var(x.to_owned())),
            free: vec![x.to_owned()],
        }
    }

    pub fn z() -> Self {
        ExprVars {
            e: Rc::new(Expr::Z),
            free: vec![],
        }
    }

    pub fn s(self) -> Self {
        ExprVars {
            e: Rc::new(Expr::S(self.e)),
            free: self.free,
        }
    }

    pub fn add(self, other: Self) -> Self {
        ExprVars {
            e: Rc::new(Expr::Add(self.e, other.e)),
            free: merge_lists(self.free, other.free),
        }
    }

    pub fn mul(self, other: Self) -> Self {
        ExprVars {
            e: Rc::new(Expr::Mul(self.e, other.e)),
            free: merge_lists(self.free, other.free),
        }
    }

    pub fn eq(self, other: Self) -> FormulaVars {
        FormulaVars {
            f: Rc::new(Formula::Eq(self.e, other.e)),
            free: merge_lists(self.free, other.free),
            bound: vec![],
        }
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

    pub fn falsehood() -> Self {
        FormulaVars {
            f: Rc::new(Formula::False),
            free: vec![],
            bound: vec![],
        }
    }

    pub fn imp(self, other: Self) -> Result<Self, SyntaxError> {
        let free = merge_lists(self.free, other.free);
        let bound = merge_lists(self.bound, other.bound);
        if let Some(x) = list_intersect(&free, &bound) {
            return Err(SyntaxError::MixingFreeAndBound(x));
        }
        Ok(FormulaVars {
            f: Rc::new(Formula::Imp(self.f, other.f)),
            free,
            bound,
        })
    }

    pub fn forall(self, x: &str) -> Result<Self, SyntaxError> {
        if self.bound.iter().any(|y| y == x) {
            return Err(SyntaxError::BoundTwice(x.to_owned()));
        }
        let free = list_remove(self.free, x);
        let mut bound = self.bound;
        bound.push(x.to_owned());
        Ok(FormulaVars {
            f: Rc::new(Formula::ForAll(x.to_owned(), self.f)),
            free,
            bound,
        })
    }

    pub fn memo(self) -> Self {
        let free = self.free.clone();
        let bound = self.bound.clone();
        FormulaVars {
            f: Rc::new(Formula::Memo(self)),
            free,
            bound,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::ExprVars;

    #[test]
    fn forall_different_vars_ok() {
        let _ = ExprVars::var("x")
            .eq(ExprVars::var("y"))
            .forall("x")
            .unwrap()
            .forall("y")
            .unwrap();
    }

    #[test]
    fn forall_same_var_not_ok() {
        assert!(ExprVars::var("x")
            .eq(ExprVars::var("y"))
            .forall("x")
            .unwrap()
            .forall("x")
            .is_err());
    }

    #[test]
    fn mixing_bound_unbound_not_ok() {
        let f = ExprVars::var("x")
            .eq(ExprVars::var("x"))
            .forall("x")
            .unwrap();
        let g = ExprVars::var("x").eq(ExprVars::var("x"));
        assert!(f.imp(g).is_err());
    }
}
