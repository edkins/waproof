use std::collections::HashMap;
use lang_stuff::{Error,Word,PosFromEnd};
use crate::ast::{Expr,Func,FuncBodyOpt,Module,Type};
use crate::semantic::{Exp,ExpBody,Name,OuterEnv,Typ};

fn to_name(w: &Word) -> Name {
    Name::Str(w.string.clone())
}

impl Type {
    fn to_typ(&self) -> Typ {
        match self {
            Type::Nat(_) => Typ::Nat,
            Type::Bool(_) => Typ::Bool,
        }
    }
}

struct InnerEnv {
    outer: OuterEnv,
    inner: HashMap<String,usize>,
    typs: Vec<Typ>,
}

fn err(pos: PosFromEnd, msg: String) -> Error {
    Error {
        msg,
        positions: vec![pos]
    }
}

impl InnerEnv {
    fn from_outer(outer: &OuterEnv) -> Self {
        InnerEnv {
            outer: outer.clone(),
            inner: HashMap::new(),
            typs: vec![]
        }
    }
    fn add(&mut self, string: &str, typ: Typ, pos: PosFromEnd) -> Result<(),Error> {
        let name = Name::Str(string.to_owned());
        if self.outer.contains_key(&name) {
            return Err(err(pos,format!("Name {} is already used in outer env", string)));
        }
        if self.inner.contains_key(string) {
            return Err(err(pos,format!("Name {} is already used in inner env", string)));
        }
        self.inner.insert(string.to_owned(), self.typs.len());
        self.typs.push(typ);
        Ok(())
    }
    fn lookup(&self, string: &str, pos: PosFromEnd) -> Result<Exp,Error> {
        let name = Name::Str(string.to_owned());
        if let Some(t) = self.outer.get(&name) {
            Ok(self.closure(t.clone(), ExpBody::Const(name)))
        } else if let Some(i) = self.inner.get(string) {
            Ok(self.closure(self.typs[*i].clone(), ExpBody::Var(*i)))
        } else {
            Err(err(pos,format!("Name {} is not defined", string)))
        }
    }
    fn closure(&self, ty: Typ, body: ExpBody) -> Exp {
        Exp{ty, body, free_vars: self.typs.clone()}
    }
}

pub fn check_module(m: &Module) -> Result<(),Error> {
    let mut oenv = create_outer_env();
    for f in &m.funcs {
        let (name,exp) = check_fn(&oenv, f)?;
        oenv.insert(name, exp.ty);
    }
    Ok(())
}

pub fn check_fn(oenv: &OuterEnv, f: &Func) -> Result<(Name,Exp),Error> {
    let mut lenv = InnerEnv::from_outer(oenv);
    for arg in &f.args {
        lenv.add(&arg.name.string, arg.ty.to_typ(), arg.name.pos())?;
    }
    let be;
    match &f.body {
        FuncBodyOpt::Body(b) => {
            be = check_expr(&lenv, &b.expr)?;
        }
        FuncBodyOpt::Semicolon(s) => {
            return Err(err(s.0.start, "Expected function body".to_owned()));
        }
    }
    let name = to_name(&f.name);
    if oenv.contains_key(&name) {
        return Err(err(f.name.pos(),format!("Function name {} is already used in outer env", f.name.string)));
    }
    Ok((name,be))
}

fn check_expr(env: &InnerEnv, main_expr:&Expr) -> Result<Exp,Error> {
    match main_expr {
        Expr::Num(n) => {
            Ok(env.closure(Typ::Nat, ExpBody::Const(Name::Num(n.n.clone()))))
        }
        Expr::Assert(assert,a,mb,_semicolon,r) => {
            let ae = check_expr(env, a)?;
            let be;
            if let Some(b) = mb {
                be = check_expr(env, &b.expr)?;
            } else {
                return Err(err(assert.0.start, "Expected 'by' clause".to_owned()));
            }
            let re = check_expr(env, r)?;
            if ae.ty != Typ::Bool {
                return Err(err(assert.0.start, format!("Expected asserted expression to have type bool, got {:?}", ae.ty)));
            }
            if be.ty != Typ::Empty {
                return Err(err(assert.0.start, format!("Expected by clause to have empty type, got {:?}", be.ty)));
            }
            Ok(env.closure(re.ty.clone(), ExpBody::Assert(Box::new(ae), Box::new(be), Box::new(re))))
        }
        Expr::Conclude(conclude,a,mb) => {
            let ae = check_expr(env, a)?;
            let be;
            if let Some(b) = mb {
                be = check_expr(env, &b.expr)?;
            } else {
                return Err(err(conclude.0.start, "Expected 'by' clause".to_owned()));
            }
            if ae.ty != Typ::Bool {
                return Err(err(conclude.0.start, format!("Expected asserted expression to have type bool, got {:?}", ae.ty)));
            }
            if be.ty != Typ::Empty {
                return Err(err(conclude.0.start, format!("Expected by clause to have empty type, got {:?}", be.ty)));
            }
            Ok(env.closure(Typ::Empty, ExpBody::Conclude(Box::new(ae), Box::new(be))))
        }
        Expr::Call(f,_,xs,_) => {
            call(env, &f.string, &xs.iter().map(|a|&a.expr).collect::<Vec<_>>(), f.pos())
        }
        Expr::Var(x) => {
            env.lookup(&x.string, x.pos())
        }
        Expr::Paren(_,x,_) => {
            check_expr(env,x)
        }
        Expr::Eq(x,o,y) => {
            call(env, "==", &[&**x,&**y], o.0.start)
        }
        Expr::Imp(x,o,y) => {
            call(env, "->", &[&**x,&**y], o.0.start)
        }
    }
}

fn call(env: &InnerEnv, f: &str, xs: &[&Expr], pos: PosFromEnd) -> Result<Exp,Error> {
    let rett;
    let fe = env.lookup(f, pos)?;
    let xes = xs.iter().map(|x|check_expr(env,x)).collect::<Result<Vec<_>,Error>>()?;
    if let Typ::Func(ats, rt) = &fe.ty {
        if ats.len() != xes.len() {
            return Err(err(pos,format!("Expected function to be called with {} arguments, got {}", ats.len(), xes.len())));
        }
        for i in 0..ats.len() {
            if xes[i].ty != ats[i] {
                return Err(err(pos,format!("Expected argument {} to be of type {:?}, got {:?}", i, ats[i], xes[i].ty)));
            }
        }
        rett = *rt.clone();
    } else {
        return Err(err(pos,format!("Item being called is not a function. Type is {:?}", fe.ty)));
    }
    Ok(env.closure(rett, ExpBody::Call(Box::new(fe),xes)))
}

fn create_outer_env() -> OuterEnv {
    let mut m = HashMap::new();
    m.insert(Name::Str("->".to_owned()), Typ::Func(vec![Typ::Bool,Typ::Bool],Box::new(Typ::Bool)));
    m.insert(Name::Str("a1".to_owned()), Typ::Func(vec![Typ::Bool,Typ::Bool],Box::new(Typ::Empty)));
    m.insert(Name::Str("a2".to_owned()), Typ::Func(vec![Typ::Bool,Typ::Bool,Typ::Bool],Box::new(Typ::Empty)));
    m.insert(Name::Str("mp".to_owned()), Typ::Func(vec![Typ::Nat,Typ::Nat],Box::new(Typ::Empty)));
    m
}
