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
    pub head: Label,
    pub left: Vec<Value>,
    pub right: Value,
}

fn write_separated_values(f: &mut std::fmt::Formatter, xs: &[Value]) -> std::fmt::Result {
    let mut first = true;
    for x in xs {
        if !first {
            write!(f, ",")?;
        }
        first = false;
        write!(f, "{}", x)?;
    }
    Ok(())
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Value::Num(n) => write!(f, "{}", n),
            Value::Str(s) => write!(f, "{}", s),
            Value::List(xs) => {
                write!(f, "[")?;
                write_separated_values(f, xs)?;
                write!(f, "]")?;
                Ok(())
            }
        }
    }
}

impl std::fmt::Display for Query {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.head)?;
        if self.left.len() > 0 {
            write!(f, "(")?;
            write_separated_values(f, &self.left)?;
            write!(f, ")")?;
        }
        write!(f, "=> {}", self.right)?;
        Ok(())
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
}

impl Expansion {
    pub fn to_query(&self, script: &Script) -> Result<Query, SemanticError> {
        let (head,left) = match &self.left {
            Expr::Num(n) => (Label::Num(n.n.clone()), vec![]),
            Expr::Call(f,_,xs,_) => (Label::Str(f.string.clone()), xs.0.iter().map(|(e,_)|e.to_value(script)).collect::<Result<_,_>>()?),
            Expr::Word(x) => (Label::Str(x.string.clone()), vec![]),
            Expr::HashWord(_,w) => return Err(SemanticError::ScriptImmutable(w.string.clone())),
            Expr::List(_,xs,_) => (Label::List, xs.0.iter().map(|(e,_)|e.to_value(script)).collect::<Result<_,_>>()?),
        };
        let right = self.right.to_value(script)?;
        Ok(Query{head,left,right})
    }
}

#[derive(Debug)]
pub enum QueryError {
    UnexpectedArityError,
    UnexpectedNotDefined,
    Nondeterminism,
    NotImplementedBuiltin,
}

impl std::error::Error for QueryError {}

impl std::fmt::Display for QueryError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl Value {
    fn is_num(&self, n: &BigUint) -> bool {
        match self {
            Value::Num(n2) => n == n2,
            _ => false
        }
    }
    fn is_string(&self, s: &str) -> bool {
        match self {
            Value::Str(s2) => s == s2,
            _ => false
        }
    }
}

impl Script {
    fn eval_query_and_add(&self, left: &Form, right: &Value, evals: &mut HashMap<Form,Value>) -> Result<bool, QueryError> {
        if self.eval_query(left, right, evals)? {
            match evals.get(left) {
                Some(x) => Ok(x == right),
                None => {
                    evals.insert(left.clone(), right.clone());
                    Ok(true)
                }
            }
        } else {
            Ok(false)
        }
    }
    fn eval_form_and_add(&self, left: &Form, evals: &mut HashMap<Form,Value>) -> Result<Option<Value>, QueryError> {
        if let Some(v) = evals.get(left) {
            return Ok(Some(v.clone()));
        }
        if let Some(v) = self.eval_form(left, evals)? {
            evals.insert(left.clone(), v);
            Ok(Some(v))
        } else {
            Ok(None)
        }
    }
    fn eval_form(&self, left: &Form, evals: &mut HashMap<Form,Value>) -> Result<Option<Value>, QueryError> {
        match &left.head {
            Label::Num(n) => {
                if !left.tail.is_empty() {
                    return Err(QueryError::UnexpectedArityError);
                }
                Ok(Some(Value::Num(n.clone())))
            }
            Label::List => {
                let mut vs = vec![];
                for x in &left.tail {
                    if let Some(v) = self.eval_form_and_add(x, evals)? {
                        vs.push(v);
                    } else {
                        return Ok(None);
                    }
                }
                Ok(Some(Value::List(vs)))
            }
            Label::Str(s) => {
                match self.0.get(s) {
                    None => Err(QueryError::UnexpectedNotDefined),
                    Some(DefinitionStatus::Terminal) => {
                        Ok(Some(Value::Str(s.clone())))
                    }
                    Some(DefinitionStatus::Builtin(_)) => {
                        Err(QueryError::NotImplementedBuiltin)
                    }
                    Some(DefinitionStatus::Nonterminal(nleft, nright)) => {
                        if left.tail.len() != nleft.len() {
                            return Err(QueryError::UnexpectedArityError);
                        }
                        let mut vs = vec![];
                        for x in &left.tail {
                            if let Some(v) = self.eval_form_and_add(x, evals)? {
                                vs.push(v);
                            } else {
                                return Ok(None);
                            }
                        }

                        let mut evals2 = HashMap::new();
                        for i in 0..vs.len() {
                            if !self.eval_query_and_add(&nleft[i], &vs[i], &mut evals2)? {
                                return Ok(None);
                            }
                        }
                        for nr in nright {
                            if let Some(v) = self.eval_form_and_add(nr, &mut evals2.clone())? {
                                return Ok(Some(v));
                            }
                        }
                        Ok(None)    // None if we don't match any options
                    }
                }
            }
        }
    }
}

impl Query {
    pub fn eval(&self, script: &Script) -> Result<bool, QueryError> {
        match &self.head {
            Label::Num(n) => {
                if !self.left.is_empty() {
                    return Err(QueryError::UnexpectedArityError);
                }
                Ok(self.right.is_num(n))
            }
            Label::List => {
                match &self.right {
                    Value::List(xs) => Ok(&self.left == xs),
                    _ => Ok(false)
                }
            }
            Label::Str(s) => {
                match script.0.get(s) {
                    None => Err(QueryError::UnexpectedNotDefined),
                    Some(DefinitionStatus::Terminal) => {
                        if !self.left.is_empty() {
                            return Err(QueryError::UnexpectedArityError);
                        }
                        Ok(self.right.is_string(s))
                    }
                    Some(DefinitionStatus::Builtin(_)) => {
                        Err(QueryError::NotImplementedBuiltin)
                    }
                    Some(DefinitionStatus::Nonterminal(nleft, nright)) => {
                        if self.left.len() != nleft.len() {
                            return Err(QueryError::UnexpectedArityError);
                        }
                        let mut evals = HashMap::new();
                        for i in 0..self.left.len() {
                            if !script.eval_query_and_add(&nleft[i], &self.left[i], &mut evals)? {
                                return Ok(false);
                            }
                        }
                        for nr in nright {
                            if script.eval_query_and_add(nr, &self.right, &mut evals.clone())? {
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
