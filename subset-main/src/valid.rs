use num_bigint::BigUint;
use std::collections::HashMap;

#[derive(Clone,Debug,Eq,PartialEq)]
pub struct ValidExpr {
    context: ValidContext,
    typ: String,
    expr: Expr,
}

#[derive(Clone,Debug,Eq,PartialEq)]
pub struct ValidContext{
    funcs: HashMap<String,FuncType>,
    types: HashMap<String,TypeDef>,
}

#[derive(Debug)]
pub enum ValidationError {
    // Errors with a Rust compiler equivalent
    E0063MissingField(usize,usize),  // field names collapsed to integers, so this means too few fields supplied
    E0308MismatchedTypes(String,String),   // multiple places
    E0308MismatchInteger(String),
    E0412NotInScope(String),
    E0422NotInScopeStruct(String),
    E0428Redefined(String),
    E0560DoesNotHaveThisField(usize,usize),  // field names collapsed to integers, so this means too many fields supplied
    E0574NotAStructType(String),
    // My own errors
    MyMismatchedContext,
}

#[derive(Clone,Debug,Eq,PartialEq)]
pub struct FuncType {
    pub args: Vec<String>,
    pub res: String,
}

#[derive(Clone,Debug,Eq,PartialEq)]
pub enum TypeDef {
    Nat,
    Struct(Vec<String>),
}

#[derive(Clone,Debug,Eq,PartialEq)]
pub enum Expr {
    Nat(BigUint),
    Struct(String, Vec<Expr>),
}

impl ValidContext {
    pub fn empty() -> Self {
        ValidContext {
            funcs: HashMap::new(),
            types: HashMap::new(),
        }
    }

    pub fn funcs(&self) -> &HashMap<String,FuncType> {
        &self.funcs
    }

    pub fn types(&self) -> &HashMap<String,TypeDef> {
        &self.types
    }

    pub fn add_nat_type(&mut self, name: &str) -> Result<(),ValidationError> {
        if self.types.contains_key(name) {
            return Err(ValidationError::E0428Redefined(name.to_owned()));
        }
        self.types.insert(name.to_owned(), TypeDef::Nat);
        Ok(())
    }

    pub fn add_struct_type(&mut self, name: &str, fields: &[&str]) -> Result<(),ValidationError> {
        if self.types.contains_key(name) {
            return Err(ValidationError::E0428Redefined(name.to_owned()));
        }
        let mut field_strings = vec![];
        for field in fields {
            if !self.types.contains_key(*field) {
                return Err(ValidationError::E0412NotInScope((*field).to_owned()));
            }
            field_strings.push((*field).to_owned());
        }
        self.types.insert(name.to_owned(), TypeDef::Struct(field_strings));
        Ok(())
    }

    pub fn nat(&self, typ: &str, value: BigUint) -> Result<ValidExpr,ValidationError> {
        match self.types.get(typ) {
            Some(TypeDef::Nat) => {
                Ok(ValidExpr{
                    context: self.clone(),
                    typ: typ.to_owned(),
                    expr: Expr::Nat(value),
                })
            }
            None => Err(ValidationError::E0412NotInScope(typ.to_owned())),
            _ => Err(ValidationError::E0308MismatchInteger(typ.to_owned())),
        }
    }

    pub fn structure(&self, name: &str, fields: &[ValidExpr]) -> Result<ValidExpr,ValidationError> {
        let struct_fields = match self.types.get(name) {
            Some(TypeDef::Struct(fs)) => fs,
            None => return Err(ValidationError::E0422NotInScopeStruct(name.to_owned())),
            _ => return Err(ValidationError::E0574NotAStructType(name.to_owned())),
        };
        if fields.len() < struct_fields.len() {
            return Err(ValidationError::E0063MissingField(struct_fields.len(), fields.len()));
        }
        if fields.len() > struct_fields.len() {
            return Err(ValidationError::E0560DoesNotHaveThisField(struct_fields.len(), fields.len()));
        }
        for i in 0..fields.len() {
            if fields[i].typ != struct_fields[i] {
                return Err(ValidationError::E0308MismatchedTypes(struct_fields[i].clone(), fields[i].typ.clone()));
            }
            if fields[i].context != *self {
                return Err(ValidationError::MyMismatchedContext);
            }
        }
        Ok(ValidExpr{
            context: self.clone(),
            typ: name.to_owned(),
            expr: Expr::Struct(name.to_owned(), fields.iter().map(|e|e.expr.clone()).collect()),
        })
    }
}
