use std::collections::HashMap;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Asm {
    I32Const(u32, Tactic),
    I32Add(Tactic),
    I8Load(u32, u32, Tactic),
    LocalGet(u32, Tactic),
    LocalSet(u32, Tactic),
    Loop(BlockType, Tactic),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Type {
    I32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum BlockType {
    None,
}

#[derive(Clone, Eq, Hash, PartialEq)]
pub enum Param {
    Param(usize),
    Hidden(usize),
}

impl std::fmt::Debug for Param {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Param::Param(i) => write!(f, "P{}", i),
            Param::Hidden(i) => write!(f, "H{}", i),
        }
    }
}

impl Param {
    pub fn expr(&self) -> Expr {
        Expr::Param(self.clone())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FullType {
    I32,
    I8Slice(VarExpr),
}

impl FullType {
    pub fn typ(&self) -> Type {
        match self {
            FullType::I32 | FullType::I8Slice(_) => Type::I32,
        }
    }

    pub fn is_address(&self) -> bool {
        match self {
            FullType::I32 => false,
            FullType::I8Slice(_) => true,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Func {
    pub params: Vec<FullType>,
    pub result: Option<FullType>,
    pub locals: Vec<Type>,
    pub hidden: Vec<FullType>,
    pub preconditions: Vec<Expr>,
    pub body: Vec<Asm>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Tactic {
    Default,
    BasePlusOffset,
    Loop(Vec<LoopTactic>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LoopTactic {
    Hidden(FullType),
    Local(usize, VarExpr),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Expr {
    Const(u32),
    Param(Param),
    Le(Box<Expr>, Box<Expr>),
    Lt(Box<Expr>, Box<Expr>),
    U32Lt(VarExpr, VarExpr),
}

impl Expr {
    pub fn le(self, other: Self) -> Self {
        Expr::Le(Box::new(self), Box::new(other))
    }

    pub fn lt(self, other: Self) -> Self {
        Expr::Lt(Box::new(self), Box::new(other))
    }
}

#[derive(Clone, Eq, PartialEq)]
pub enum VarExpr {
    I32Linear(u32, Vec<(Param, u32)>),
}

impl std::fmt::Debug for VarExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            VarExpr::I32Linear(k, xs) => {
                write!(f, "{}", *k as i32)?;
                for (x, n) in xs {
                    write!(f, "{:+}{:?}", *n as i32, x)?;
                }
            }
        }
        Ok(())
    }
}

impl VarExpr {
    pub fn typ(&self) -> Type {
        match self {
            VarExpr::I32Linear(_, _) => Type::I32,
        }
    }

    pub fn panic_unless_i32(&self) {
        if self.typ() != Type::I32 {
            panic!("Expected i32, got {:?}", self.typ());
        }
    }

    pub fn i32_add(&self, other: &Self) -> Self {
        match (self, other) {
            (VarExpr::I32Linear(k0, xs0), VarExpr::I32Linear(k1, xs1)) => {
                let k = k0.wrapping_add(*k1);
                let mut map: HashMap<Param, u32> = HashMap::new();
                for (x, n) in xs0.iter().chain(xs1.iter()) {
                    let value = map.entry(x.clone()).or_insert(0);
                    *value = value.wrapping_add(*n);
                }
                let xs = map
                    .iter()
                    .filter(|(x, n)| **n != 0)
                    .map(|(x, n)| (x.clone(), n.clone()))
                    .collect();
                VarExpr::I32Linear(k, xs)
            } //_ => panic!("i32_add: expected two i32's")
        }
    }

    pub fn i32_sub(&self, other: &Self) -> Self {
        self.i32_add(&other.i32_neg())
    }

    pub fn i32_neg(&self) -> Self {
        self.i32_scale(u32::MAX)
    }

    pub fn i32_scale(&self, scale: u32) -> Self {
        match self {
            VarExpr::I32Linear(k, xs) => VarExpr::I32Linear(
                k.wrapping_mul(scale),
                xs.iter()
                    .map(|(x, n)| (x.clone(), n.wrapping_mul(scale)))
                    .filter(|(x, n)| *n != 0)
                    .collect(),
            ), //_ => panic!("i32_scale: expected i32")
        }
    }

    pub fn u32_lt(&self, other: &Self) -> Expr {
        Expr::U32Lt(self.clone(), other.clone())
    }

    pub fn zero() -> Self {
        VarExpr::I32Linear(0, vec![])
    }

    pub fn i32const(k: u32) -> Self {
        VarExpr::I32Linear(k, vec![])
    }

    pub fn i32param(i: usize) -> Self {
        VarExpr::I32Linear(0, vec![(Param::Param(i), 1)])
    }

    pub fn i32hidden(i: usize) -> Self {
        VarExpr::I32Linear(0, vec![(Param::Hidden(i), 1)])
    }

    pub fn i32param_or_hidden(p: &Param) -> Self {
        VarExpr::I32Linear(0, vec![(p.clone(), 1)])
    }
}
