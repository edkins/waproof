use num_bigint::BigUint;
use std::collections::HashMap;

use crate::ast::{Expr,Expansion};
use crate::semantics::{DefinitionStatus,Form,Label,SemanticError,Script};

#[derive(Clone,Debug,PartialEq,Eq)]
pub enum Value {
    Num(BigUint),
    Str(String),
    List(Vec<Value>),
}

#[derive(Clone,Debug)]
pub struct Query {
    pub left: Form,
    pub right: Value,
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Value::Num(n) => write!(f, "{}", n),
            Value::Str(s) => write!(f, "{}", s),
            Value::List(xs) => {
                write!(f, "[")?;
                let mut first = true;
                for x in xs {
                    if !first {
                        write!(f, ",")?;
                    }
                    first = false;
                    write!(f, "{}", x)?;
                }
                write!(f, "]")?;
                Ok(())
            }
        }
    }
}

impl std::fmt::Display for Query {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{} => {}", self.left, self.right)
    }
}

impl Expr {
    fn to_value(&self, script: &Script) -> Result<Value,SemanticError> {
        match self {
            Expr::Num(n) => Ok(Value::Num(n.n.clone())),
            Expr::Word(w) => {
                match script.0.get(&w.string) {
                    Some(DefinitionStatus::Terminal) => Ok(Value::Str(w.string.clone())),
                    Some(_) => Err(SemanticError::NotTerminal(w.string.clone())),
                    None => Err(SemanticError::Undefined(w.string.clone())),
                }
            }
            Expr::List(_,xs,_) => {
                let tail = xs.0.iter().map(|(e,_)|e.to_value(script)).collect::<Result<_,_>>()?;
                Ok(Value::List(tail))
            }
            _ => Err(SemanticError::NotAValue(format!("{}", self))),
        }
    }

    // TODO: it would be nice not to have to duplicate all this code for the immutable case

    fn to_head_tail_immut(&self, script: &Script) -> Result<(String,Vec<Form>), SemanticError> {
        match self {
            Expr::Call(w,_,es,_) => {
                let tail = es.0.iter().map(|(e,_)|e.to_form_immut(script)).collect::<Result<_,_>>()?;
                Ok((w.string.clone(),tail))
            }
            Expr::Word(w) => {
                Ok((w.string.clone(),vec![]))
            }
            _ => Err(SemanticError::NotHeadTail(format!("{}", self)))
        }
    }

    fn to_form_immut(&self, script: &Script) -> Result<Form,SemanticError> {
        match self {
            Expr::Num(n) => {
                let head = Label::Num(n.n.clone());
                Ok(Form{ head, tail: vec![] })
            }
            Expr::Call(_,_,_,_) | Expr::Word(_) => {
                let (head,tail) = self.to_head_tail_immut(script)?;
                match script.0.get(&head) {
                    Some(DefinitionStatus::Terminal) => {
                        if !tail.is_empty() { 
                            return Err(SemanticError::ArityMismatch(head,0,tail.len()));
                        }
                    }
                    Some(DefinitionStatus::Nonterminal(left,_)) | Some(DefinitionStatus::Builtin(left)) => {
                        if tail.len() != left.len() {
                            return Err(SemanticError::ArityMismatch(head,left.len(),tail.len()));
                        }
                    }
                    None => return Err(SemanticError::Undefined(head))
                }
                let head = Label::Str(head);
                Ok(Form{ head, tail })
            }
            Expr::HashWord(_,w) => Err(SemanticError::ScriptImmutable(w.string.clone())),
            Expr::List(_,xs,_) => {
                let tail = xs.0.iter().map(|(e,_)|e.to_form_immut(script)).collect::<Result<_,_>>()?;
                Ok(Form{ head: Label::List, tail })
            }
        }
    }
}

impl Expansion {
    pub fn to_query(&self, script: &Script) -> Result<Query, SemanticError> {
        let left = self.left.to_form_immut(script)?;
        let right = self.right.to_value(script)?;
        Ok(Query{left,right})
    }
}

#[derive(Debug)]
pub enum QueryError {
    UnexpectedArityError,
    UnexpectedNotDefined,
    NotImplementedBuiltin,
    NotImplementedParam,
}

impl std::error::Error for QueryError {}

impl std::fmt::Display for QueryError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Script {
    fn eval_query_and_add(&self, left: &Form, right: &Value, evals: &mut HashMap<Form,Value>) -> Result<bool, QueryError> {
        if self.eval_query(left, right, evals)? {
            if let Some(x) = evals.get(left) {
                Ok(x == right)
            } else {
                evals.insert(left.clone(), right.clone());
                Ok(true)
            }
        } else {
            Ok(false)
        }
    }
    fn eval_query(&self, left: &Form, right: &Value, evals: &mut HashMap<Form,Value>) -> Result<bool, QueryError> {
        match &left.head {
            Label::Num(n) => {
                if !left.tail.is_empty() {
                    return Err(QueryError::UnexpectedArityError);
                }
                match right {
                    Value::Num(n2) => Ok(n == n2),
                    _ => Ok(false)
                }
            }
            Label::List => {
                let xs = &left.tail;
                match right {
                    Value::List(ys) => {
                        if xs.len() != ys.len () {
                            return Ok(false);
                        }
                        for i in 0..xs.len() {
                            if !self.eval_query_and_add(&xs[i], &ys[i], evals)? {
                                return Ok(false);
                            }
                        }
                        Ok(true)
                    }
                    _ => Ok(false)
                }
            }
            Label::Str(s) => {
                match self.0.get(s) {
                    None => Err(QueryError::UnexpectedNotDefined),
                    Some(DefinitionStatus::Terminal) => {
                        if !left.tail.is_empty() {
                            return Err(QueryError::UnexpectedArityError);
                        }
                        match right {
                            Value::Str(s2) => Ok(s == s2),
                            _ => Ok(false)
                        }
                    }
                    Some(DefinitionStatus::Builtin(_)) => {
                        Err(QueryError::NotImplementedBuiltin)
                    }
                    Some(DefinitionStatus::Nonterminal(nleft, nright)) => {
                        if left.tail.len() != nleft.len() {
                            return Err(QueryError::UnexpectedArityError);
                        }
                        if left.tail.len() != 0 {
                            // Parametric stuff is harder to implement
                            return Err(QueryError::NotImplementedParam);
                        }
                        for nr in nright {
                            let mut clone = evals.clone();
                            if self.eval_query_and_add(nr, right, &mut clone)? {
                                return Ok(true);
                            }
                        }
                        Ok(false)    // false if we don't match any options
                    }
                }
            }
        }
    }
}

impl Query {
    pub fn eval(&self, script: &Script) -> Result<bool, QueryError> {
        let mut evals = HashMap::new();
        script.eval_query_and_add(&self.left, &self.right, &mut evals)
    }
}
