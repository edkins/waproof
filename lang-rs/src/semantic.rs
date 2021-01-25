use num_bigint::BigUint;
use std::collections::HashMap;

#[derive(Clone,Eq,Hash,PartialEq)]
pub enum Name {
    Str(String),
    Num(BigUint),
}

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
pub enum ExpBody {
    Var(usize),
    Const(Name),
    Call(Box<Exp>,Vec<Exp>),
    Lambda(Vec<Typ>,Box<Exp>),
    Assert(Box<Exp>,Box<Exp>,Box<Exp>),
    Conclude(Box<Exp>,Box<Exp>),
    Mp(usize,usize),
    Primitive,
}

pub type OuterEnv = HashMap<Name,Exp>;
