use num_bigint::BigUint;
use std::collections::HashMap;
use std::fmt;

#[derive(Clone,Debug,Eq,PartialEq)]
pub enum Typ {
    Empty,
    Bool,
    Nat,
    Func(Vec<Typ>,Box<Typ>),
}

#[derive(Clone,Eq,PartialEq)]
pub struct Exp {
    pub ty: Typ,
    pub free_vars: Vec<Typ>,
    pub body: ExpBody,
}

#[derive(Clone,Eq,PartialEq)]
pub enum CallHead {
    Num(BigUint),
    Const(String),
    Param(String),
}

#[derive(Clone,Eq,PartialEq)]
pub enum ExpBody {
    Var(usize),
    Const(CallHead),
    Call(CallHead,Vec<Exp>),
    Lambda(Vec<Typ>,Box<Exp>),
    Assert(Box<Exp>,Box<Exp>,Box<Exp>),
    Conclude(Box<Exp>,Box<Exp>),
    Mp(usize,usize),
    Primitive,
}

#[derive(Clone)]
pub struct TheoremSchema {
    pub params: Vec<(String,Typ)>,
    pub conc: Exp,
}

#[derive(Clone)]
pub struct OEnvThing {
    pub ty: Typ,
    pub theorem: Option<TheoremSchema>,
}

pub type OuterEnv = HashMap<String,OEnvThing>;

impl fmt::Display for CallHead {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CallHead::Num(n) => write!(f, "{}", n),
            CallHead::Const(c) => write!(f, "#{}", c),
            CallHead::Param(p) => write!(f, "${}", p),
        }
    }
}

impl fmt::Display for Exp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.body {
            ExpBody::Var(i) => write!(f, "x{}", i),
            ExpBody::Const(c) => write!(f, "{}", c),
            ExpBody::Call(c,xs) => {
                write!(f, "{}(", c)?;
                for x in xs {
                    write!(f, "{},", x)?;
                }
                write!(f, ")")
            }
            ExpBody::Assert(e,b,r) => write!(f, "assert({}) by {}; {}", e, b, r),
            ExpBody::Conclude(e,b) => write!(f, "conclude({}) by {}", e, b),
            ExpBody::Primitive => write!(f, "primitive"),
            ExpBody::Lambda(ts,x) => write!(f, "|{:?}| {}", ts, x),
            ExpBody::Mp(a,b) => write!(f, "mp({},{})", a, b),
        }
    }
}
