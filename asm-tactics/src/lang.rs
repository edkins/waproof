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

#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
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
    pub fn i32_load8(&self, i: &VarExpr) -> VarTerm {
        VarTerm::I32Load8(self.clone(), Box::new(i.clone()))
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
    U32Lt(VarExpr, VarExpr),
}

#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
pub enum VarTerm {
    Param(usize),
    Hidden(usize),
    I32Load8(Param, Box<VarExpr>),
}

impl std::fmt::Debug for VarTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            VarTerm::Param(i) => write!(f, "p{}", i),
            VarTerm::Hidden(i) => write!(f, "p{}", i),
            VarTerm::I32Load8(p, e) => write!(f, "{:?}[{:?}]", p, e),
        }
    }
}

impl VarTerm {
    pub fn as_param(&self) -> Param {
        match self {
            VarTerm::Param(i) => Param::Param(*i),
            VarTerm::Hidden(i) => Param::Hidden(*i),
            _ => panic!("Expected param or hidden, got {:?}", self),
        }
    }
}

#[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
pub enum VarExpr {
    I32Linear(u32, Vec<(VarTerm, u32)>),
}

impl std::fmt::Debug for VarExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            VarExpr::I32Linear(k, xs) => {
                if *k != 0 {
                    write!(f, "{}", *k as i32)?;
                }
                for (x, n) in xs {
                    if *n == 1 {
                        write!(f, "+{:?}", x)?;
                    } else if *n == u32::MAX {
                        write!(f, "-{:?}", x)?;
                    } else {
                        write!(f, "{:+}{:?}", *n as i32, x)?;
                    }
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
                let mut vec = xs0.clone();
                vec.extend_from_slice(&xs1);
                vec.sort();

                let mut result = vec![];
                let mut last_x = None;
                let mut last_n = 0u32;
                for (x, n) in &vec {
                    if last_x == Some(x) {
                        last_n = last_n.wrapping_add(*n);
                    } else {
                        if last_n != 0 {
                            result.push((last_x.unwrap().clone(), last_n));
                        }
                        last_x = Some(x);
                        last_n = *n;
                    }
                }
                if last_n != 0 {
                    result.push((last_x.unwrap().clone(), last_n));
                }
                VarExpr::I32Linear(k, result)
            }
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
                    .filter(|(_, n)| *n != 0)
                    .collect(),
            ),
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
        VarExpr::I32Linear(0, vec![(VarTerm::Param(i), 1)])
    }

    pub fn i32hidden(i: usize) -> Self {
        VarExpr::I32Linear(0, vec![(VarTerm::Hidden(i), 1)])
    }

    pub fn i32term(t: &VarTerm) -> Self {
        VarExpr::I32Linear(0, vec![(t.clone(), 1)])
    }
}
