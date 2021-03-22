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

#[derive(Clone, Eq, PartialEq)]
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
    I8Slice(Param),
}

impl FullType {
    pub fn typ(&self) -> Type {
        match self {
            FullType::I32 | FullType::I8Slice(_) => Type::I32,
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
    I32Const(u32),
    I32Param(Param),
    I32Add(Box<VarExpr>, Box<VarExpr>),
    I32Sub(Box<VarExpr>, Box<VarExpr>),
}

impl std::fmt::Debug for VarExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            VarExpr::I32Const(n) => write!(f, "{}", n),
            VarExpr::I32Param(p) => write!(f, "{:?}", p),
            VarExpr::I32Add(a, b) => write!(f, "({:?} + {:?})", a, b),
            VarExpr::I32Sub(a, b) => write!(f, "({:?} - {:?})", a, b),
        }
    }
}

impl VarExpr {
    pub fn typ(&self) -> Type {
        match self {
            VarExpr::I32Const(_)
            | VarExpr::I32Param(_)
            | VarExpr::I32Add(_, _)
            | VarExpr::I32Sub(_, _) => Type::I32,
        }
    }

    pub fn panic_unless_i32(&self) {
        if self.typ() != Type::I32 {
            panic!("Expected i32, got {:?}", self.typ());
        }
    }
}
