use std::rc::Rc;

#[derive(Debug)]
pub enum SyntaxError {
    MixingFreeAndBound(String),
    BoundTwice(String),
    SubstBoundVar(String),
    SubstForBoundVar(String),
}

#[derive(Clone, Default, Eq, PartialEq)]
pub struct VarSet(Rc<Vec<String>>);

impl VarSet {
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn singleton(x: &str) -> Self {
        VarSet(Rc::new(vec![x.to_owned()]))
    }

    pub fn contains(&self, x: &str) -> bool {
        self.0.iter().any(|y| y == x)
    }

    pub fn slice(&self) -> &[String] {
        &self.0
    }

    pub fn example(&self) -> Option<&str> {
        if self.is_empty() {
            None
        } else {
            Some(&self.0[0])
        }
    }

    pub fn intersects<'a>(&self, other: &'a Self) -> Option<&'a str> {
        for x in other.0.iter() {
            if self.contains(x) {
                return Some(x);
            }
        }
        None
    }

    pub fn with(&self, x: &str) -> Self {
        if self.contains(x) {
            self.clone()
        } else {
            let mut vec = (*self.0).clone();
            vec.push(x.to_owned());
            VarSet(Rc::new(vec))
        }
    }

    pub fn without(&self, x: &str) -> Self {
        if !self.contains(x) {
            self.clone()
        } else {
            let vec = self.0.iter().filter(|y| y != &x).map(|y|y.clone()).collect();
            VarSet(Rc::new(vec))
        }
    }

    pub fn union(&self, other: &Self) -> Self {
        if self.is_empty() {
            other.clone()
        } else if other.is_empty() {
            self.clone()
        } else if self == other {
            self.clone()
        } else {
            let mut vec = (*self.0).clone();
            for x in other.0.iter() {
                if !vec.contains(x) {
                    vec.push(x.clone())
                }
            }
            vec.sort();
            VarSet(Rc::new(vec))
        }
    }
}

#[derive(Clone, Eq, PartialEq)]
pub struct Expr {
    e: ExprEnum,
    v: VarSet,
}

#[derive(Clone, Eq, PartialEq)]
enum ExprEnum {
    Var(String),
    Z,
    S(Rc<Expr>),
    Add(Rc<Expr>, Rc<Expr>),
    Mul(Rc<Expr>, Rc<Expr>),
}

impl std::fmt::Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.e {
            ExprEnum::Var(x) => write!(f, "{}", x),
            ExprEnum::Z => write!(f, "0"),
            ExprEnum::S(e) => write!(f, "S({:?})", e),
            ExprEnum::Add(a, b) => write!(f, "({:?}+{:?})", a, b),
            ExprEnum::Mul(a, b) => write!(f, "({:?}+{:?})", a, b),
        }
    }
}

#[derive(Clone, Eq, PartialEq)]
pub struct Formula {
    f: FormulaEnum,
    free: VarSet,
    bound: VarSet,
}

#[derive(Clone, Eq, PartialEq)]
enum FormulaEnum {
    False,
    Eq(Rc<Expr>, Rc<Expr>),
    Imp(Rc<Formula>, Rc<Formula>),
    ForAll(String, Rc<Formula>),
}

impl std::fmt::Debug for Formula {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.f {
            FormulaEnum::False => write!(f, "false"),
            FormulaEnum::Eq(a, b) => write!(f, "({:?}={:?})", a, b),
            FormulaEnum::Imp(a, b) => write!(f, "({:?} -> {:?})", a, b),
            FormulaEnum::ForAll(x, a) => write!(f, "@{}({:?})", x, a),
        }
    }
}

impl Expr {
    pub fn cases<'a, T: 'a>(
        &'a self,
        var: impl FnOnce(&'a String) -> T,
        z: impl FnOnce() -> T,
        s: impl FnOnce(&'a Expr) -> T,
        add: impl FnOnce(&'a Expr, &'a Expr) -> T,
        mul: impl FnOnce(&'a Expr, &'a Expr) -> T,
    ) -> T {
        match &self.e {
            ExprEnum::Var(x) => var(x),
            ExprEnum::Z => z(),
            ExprEnum::S(a) => s(a),
            ExprEnum::Add(a, b) => add(a, b),
            ExprEnum::Mul(a, b) => mul(a, b),
        }
    }

    pub fn free(&self) -> &VarSet {
        &self.v
    }

    pub fn has_free(&self, x: &str) -> bool {
        self.v.contains(x)
    }

    pub fn var(x: &str) -> Self {
        Expr {
            e: ExprEnum::Var(x.to_owned()),
            v: VarSet::singleton(x),
        }
    }

    pub fn z() -> Self {
        Expr {
            e: ExprEnum::Z,
            v: VarSet::default(),
        }
    }

    pub fn s(self) -> Self {
        let v = self.v.clone();
        Expr {
            e: ExprEnum::S(Rc::new(self)),
            v,
        }
    }

    pub fn add(self, other: Self) -> Self {
        let v = self.v.union(&other.v);
        Expr {
            e: ExprEnum::Add(Rc::new(self), Rc::new(other)),
            v,
        }
    }

    pub fn mul(self, other: Self) -> Self {
        let v = self.v.union(&other.v);
        Expr {
            e: ExprEnum::Mul(Rc::new(self), Rc::new(other)),
            v,
        }
    }

    pub fn eq(self, other: Self) -> Formula {
        let free = self.v.union(&other.v);
        Formula {
            f: FormulaEnum::Eq(Rc::new(self), Rc::new(other)),
            free,
            bound: VarSet::default(),
        }
    }
}

impl Formula {
    pub fn cases<'a, T: 'a>(
        &'a self,
        fals: impl FnOnce() -> T,
        eq: impl FnOnce(&'a Expr, &'a Expr) -> T,
        imp: impl FnOnce(&'a Formula, &'a Formula) -> T,
        forall: impl FnOnce(&'a str, &'a Formula) -> T,
    ) -> T {
        match &self.f {
            FormulaEnum::False => fals(),
            FormulaEnum::Eq(a, b) => eq(a, b),
            FormulaEnum::Imp(a, b) => imp(a, b),
            FormulaEnum::ForAll(x, a) => forall(x, a),
        }
    }

    pub fn falsehood() -> Self {
        Formula {
            f: FormulaEnum::False,
            free: VarSet::default(),
            bound: VarSet::default(),
        }
    }

    pub fn imp(self, other: Self) -> Result<Self, SyntaxError> {
        let free = self.free.union(&other.free);
        let bound = self.bound.union(&other.bound);
        if let Some(x) = free.intersects(&bound) {
            Err(SyntaxError::MixingFreeAndBound(x.to_owned()))
        } else {
            Ok(Formula {
                f: FormulaEnum::Imp(Rc::new(self), Rc::new(other)),
                free,
                bound,
            })
        }
    }

    pub fn forall(self, x: &str) -> Result<Self, SyntaxError> {
        if self.bound.contains(x) {
            Err(SyntaxError::BoundTwice(x.to_owned()))
        } else {
            let free = self.free.without(x);
            let bound = self.bound.with(x);
            Ok(Formula {
                f: FormulaEnum::ForAll(x.to_owned(), Rc::new(self)),
                free,
                bound,
            })
        }
    }

    pub fn free(&self) -> &VarSet {
        &self.free
    }

    pub fn has_free(&self, x: &str) -> bool {
        self.free.contains(x)
    }

    pub fn bound(&self) -> &VarSet {
        &self.bound
    }

    pub fn has_bound(&self, x: &str) -> bool {
        self.bound.contains(x)
    }
}
