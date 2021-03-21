#[derive(Clone,Debug,Eq,PartialEq)]
pub enum Asm {
    I32Const(u32, Tactic),
    I32Add(Tactic),
    I8Load(u32, u32, Tactic),
    LocalGet(u32, Tactic),
}

#[derive(Clone,Debug,Eq,PartialEq)]
pub enum Type {
    I32,
}

#[derive(Clone,Debug,Eq,PartialEq)]
pub enum Param {
    Param(usize),
    Hidden(usize),
}

impl Param {
    pub fn expr(&self) -> Expr {
        Expr::Param(self.clone())
    }
}

#[derive(Clone,Debug,Eq,PartialEq)]
pub enum FullType {
    I32,
    I8Slice(Param),
}

impl FullType {
    pub fn typ(&self) -> Type {
        match self {
            FullType::I32 |
                FullType::I8Slice(_) => Type::I32,
        }
    }
}

#[derive(Clone,Debug,Eq,PartialEq)]
pub struct Func {
    pub params: Vec<FullType>,
    pub result: Option<FullType>,
    pub locals: Vec<Type>,
    pub hidden: Vec<FullType>,
    pub preconditions: Vec<Expr>,
    pub body: Vec<Asm>,
}

#[derive(Clone,Debug,Eq,PartialEq)]
pub enum Tactic {
    Default,
    BasePlusOffset,
}

#[derive(Clone,Debug,Eq,PartialEq)]
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
