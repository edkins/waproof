use num_bigint::BigUint;
use std::collections::HashMap;
use crate::ast::{Definition,Expr,Module,Statement};

#[derive(Clone,Debug,PartialEq,Eq,Hash)]
pub enum Label {
    Num(BigUint),
    Str(String),
    List,
}

#[derive(Clone,Debug,PartialEq,Eq,Hash)]
pub struct Form {
    pub head: Label,
    pub tail: Vec<Form>,
}

#[derive(Debug)]
pub enum DefinitionStatus {
    Terminal,
    Nonterminal(Vec<Form>, Vec<Form>),
    Builtin(Vec<Form>),
}

#[derive(Debug)]
pub struct Script(pub HashMap<String,DefinitionStatus>);

#[derive(Debug)]
pub enum SemanticError {
    Undefined(String),
    AlreadyDefined(String),
    ArityMismatch(String,usize,usize),
    NotAWord(String),
    NotHeadTail(String),
    NotTerminal(String),
    NotAValue(String),
    ScriptImmutable(String),
}

impl std::fmt::Display for SemanticError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for SemanticError {
}

impl From<SemanticError> for std::io::Error {
    fn from(e: SemanticError) -> Self {
        std::io::Error::new(std::io::ErrorKind::Other, e)
    }
}

fn form(x: &str) -> Form {
    Form{head: Label::Str(x.to_owned()), tail: vec![]}
}

impl Script {
    fn new() -> Self {
        let mut defs = HashMap::new();
        defs.insert("any".to_owned(), DefinitionStatus::Builtin(vec![]));
        defs.insert("nat".to_owned(), DefinitionStatus::Builtin(vec![]));
        defs.insert("constint".to_owned(), DefinitionStatus::Builtin(vec![form("nat")]));
        defs.insert("constfloat".to_owned(), DefinitionStatus::Builtin(vec![form("nat")]));
        Self(defs)
    }

    fn add_terminal(&mut self, word: String) -> Result<(),SemanticError> {
        match self.0.get(&word) {
            Some(DefinitionStatus::Terminal) => Ok(()),
            None => {
                self.0.insert(word, DefinitionStatus::Terminal);
                Ok(())
            }
            _ => Err(SemanticError::AlreadyDefined(word))
        }
    }

    fn add_nonterminal(&mut self, word: String, left: Vec<Form>, right: Vec<Form>) -> Result<(),SemanticError> {
        if self.0.contains_key(&word) {
            return Err(SemanticError::AlreadyDefined(word));
        }
        self.0.insert(word, DefinitionStatus::Nonterminal(left,right));
        Ok(())
    }
}

impl Expr {
    fn as_word(&self) -> Result<String,SemanticError> {
        match self {
            Expr::Word(w) => Ok(w.string.clone()),
            _ => Err(SemanticError::NotAWord(format!("{}", self))),
        }
    }

    fn to_head_tail(&self, script: &mut Script) -> Result<(String,Vec<Form>), SemanticError> {
        match self {
            Expr::Call(w,_,es,_) => {
                let tail = es.0.iter().map(|(e,_)|e.to_form(script)).collect::<Result<_,_>>()?;
                Ok((w.string.clone(),tail))
            }
            Expr::Word(w) => {
                Ok((w.string.clone(),vec![]))
            }
            _ => Err(SemanticError::NotHeadTail(format!("{}", self)))
        }
    }

    fn to_form(&self, script: &mut Script) -> Result<Form,SemanticError> {
        match self {
            Expr::Num(n) => {
                let head = Label::Num(n.n.clone());
                Ok(Form{ head, tail: vec![] })
            }
            Expr::Call(_,_,_,_) | Expr::Word(_) => {
                let (head,tail) = self.to_head_tail(script)?;
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
            Expr::HashWord(_,w) => {
                script.add_terminal(w.string.clone())?;
                let head = Label::Str(w.string.clone());
                Ok(Form{ head, tail: vec![] })
            }
            Expr::List(_,xs,_) => {
                let tail = xs.0.iter().map(|(e,_)|e.to_form(script)).collect::<Result<_,_>>()?;
                Ok(Form{ head: Label::List, tail })
            }
        }
    }
}

impl Module {
    pub fn to_script(&self) -> Result<Script,SemanticError> {
        let mut script = Script::new();
        for statement in &self.statements {
            match &statement {
                Statement::Expand(terms, _, def, _) => {
                    for (term,_) in terms.0.iter() {
                        match def {
                            Definition::Exprs(es) => {
                                let (head,left) = term.to_head_tail(&mut script)?;
                                let right = es.0.iter().map(|(e,_)|e.to_form(&mut script)).collect::<Result<_,_>>()?;
                                script.add_nonterminal(head, left, right)?;
                            }
                            Definition::JustHash(_) => {
                                script.add_terminal(term.as_word()?)?;
                            }
                        }
                    }
                }
            }
        }
        Ok(script)
    }
}

impl std::fmt::Display for Label {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Label::Num(n) => write!(f, "{}", n),
            Label::Str(s) => write!(f, "{}", s),
            Label::List => write!(f, "list"),
        }
    }
}

fn write_separated_forms(f: &mut std::fmt::Formatter, xs: &[Form], sep: &str) -> std::fmt::Result {
    let mut first = true;
    for form in xs {
        if !first {
            write!(f, "{}", sep)?;
        }
        first = false;
        write!(f, "{}", form)?;
    }
    Ok(())
}

fn write_form_args(f: &mut std::fmt::Formatter, xs: &[Form]) -> std::fmt::Result {
    if xs.len() > 0 {
        write!(f, "(")?;
        write_separated_forms(f, xs, ",")?;
        write!(f, ")")?;
    }
    Ok(())
}

impl std::fmt::Display for Form {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.head {
            Label::List => {
                write!(f, "[")?;
                write_separated_forms(f, &self.tail, ",")?;
                write!(f, "]")?;
                Ok(())
            }
            _ => {
                write!(f, "{}", self.head)?;
                write_form_args(f, &self.tail)?;
                Ok(())
            }
        }
    }
}

impl std::fmt::Display for Script {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let mut keys = self.0.keys().collect::<Vec<_>>();
        keys.sort();
        for key in keys {
            match self.0.get(key).unwrap() {
                DefinitionStatus::Terminal => {write!(f, "{} ::= #.\n", key)?;}
                DefinitionStatus::Builtin(left) => {
                    write!(f, "{}", key)?;
                    write_form_args(f, left)?;
                    write!(f, " builtin.\n")?;
                }
                DefinitionStatus::Nonterminal(left,right) => {
                    write!(f, "{}", key)?;
                    write_form_args(f, left)?;
                    write!(f, " ::= ")?;
                    write_separated_forms(f, right, " | ")?;
                    write!(f, ".\n")?;
                }
            }
        }
        Ok(())
    }
}

