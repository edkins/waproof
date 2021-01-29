use std::collections::HashMap;
use std::convert::TryInto;
use lang_stuff::{Error,Word,Parse,PosFromEnd};
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

#[derive(Clone,Eq,PartialEq)]
enum FuncKind {
    Primitive,
    Axiom,
    Theorem,
}

struct InnerEnv {
    outer: OuterEnv,
    inner: HashMap<String,usize>,
    typs: Vec<Typ>,
    kind: FuncKind,
    assertions: Vec<Exp>,
}

fn err(pos: PosFromEnd, msg: String) -> Error {
    Error {
        msg,
        positions: vec![pos]
    }
}

impl InnerEnv {
    fn from_outer(outer: &OuterEnv, kind: FuncKind) -> Self {
        InnerEnv {
            outer: outer.clone(),
            inner: HashMap::new(),
            typs: vec![],
            kind,
            assertions: vec![],
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
        if let Some(e) = self.outer.get(&name) {
            Ok(self.closure(e.ty.clone(), ExpBody::Const(name)))
        } else if let Some(i) = self.inner.get(string) {
            Ok(self.closure(self.typs[*i].clone(), ExpBody::Var(*i)))
        } else {
            Err(err(pos,format!("Name {} is not defined", string)))
        }
    }
    fn lookup_conclusion(&self, name: &Name, pos: PosFromEnd) -> Result<Exp,Error> {
        if let Some(e) = self.outer.get(&name) {
            e.get_conclusion(pos)
        } else {
            Err(err(pos,format!("Name {:?} is not defined in outer environment", name)))
        }
    }
    fn closure(&self, ty: Typ, body: ExpBody) -> Exp {
        Exp{ty, body, free_vars: self.typs.clone()}
    }
}

impl Exp {
    fn get_conclusion(&self, pos: PosFromEnd) -> Result<Exp,Error> {
        match &self.body {
            ExpBody::Assert(_,_,e) => e.get_conclusion(pos),
            ExpBody::Conclude(c,_) => Ok((**c).clone()),
            _ => Err(err(pos,"Expression does not have conclusion".to_owned()))
        }
    }
}

pub fn check_module(m: &Module) -> Result<(),Error> {
    let mut oenv = create_outer_env();
    for f in &m.funcs {
        let (name,exp) = check_fn(&oenv, f, false)?;
        oenv.insert(name, exp);
    }
    Ok(())
}

fn check_fn(oenv: &OuterEnv, f: &Func, allow_axioms: bool) -> Result<(Name,Exp),Error> {
    let kind = check_fn_attributes(f, allow_axioms)?;
    let mut lenv = InnerEnv::from_outer(oenv, kind.clone());
    for arg in &f.args {
        lenv.add(&arg.name.string, arg.ty.to_typ(), arg.name.pos())?;
    }
    let expr;
    let rett = f.ret.as_ref().map(|r|r.ty.to_typ()).unwrap_or(Typ::Empty);
    match (&f.body, kind) {
        (FuncBodyOpt::Body(b), FuncKind::Theorem) |
        (FuncBodyOpt::Body(b), FuncKind::Axiom) => {
            let be = check_expr(&lenv, &b.expr)?;
            if be.ty != rett {
                return Err(err(b.open.0.start, format!("Declared return type is {:?}, actual return type is {:?}", rett, be.ty)));
            }
            expr = Exp{
                ty: Typ::Func(be.free_vars.clone(), Box::new(be.ty.clone())),
                free_vars: vec![],
                body: ExpBody::Lambda(be.free_vars.clone(), Box::new(be)),
            }
        }
        (FuncBodyOpt::Body(b), _) => {
            return Err(err(b.open.0.start, "Expected no function body".to_owned()));
        }
        (FuncBodyOpt::Semicolon(_), FuncKind::Primitive) => {
            expr = lenv.closure(Typ::Func(lenv.typs.clone(),Box::new(rett.clone())), ExpBody::Primitive);
        }
        (FuncBodyOpt::Semicolon(s), _) => {
            return Err(err(s.0.start, "Expected function body".to_owned()));
        }
    }
    let name = to_name(&f.name);
    if oenv.contains_key(&name) {
        return Err(err(f.name.pos(),format!("Function name {} is already used in outer env", f.name.string)));
    }
    Ok((name,expr))
}

fn check_fn_attributes(f: &Func, allow_axioms: bool) -> Result<FuncKind,Error> {
    if f.attrs.len() != 1 {
        return Err(err(f.fun.0.start, "Expected exactly one attribute".to_owned()));
    }
    match &f.attrs[0].word.string as &str {
        "primitive" => if allow_axioms {
            Ok(FuncKind::Primitive)
        } else {
            Err(err(f.attrs[0].word.pos(), "Reserved attribute 'primitive' not supported in this context".to_owned()))
        }
        "axiom" => if allow_axioms {
            Ok(FuncKind::Axiom)
        } else {
            Err(err(f.attrs[0].word.pos(), "Reserved attribute 'axiom' not supported in this context".to_owned()))
        }
        "theorem" => Ok(FuncKind::Theorem),
        _ => Err(err(f.attrs[0].word.pos(), format!("Unrecognized attribute {}", f.attrs[0].word)))
    }
}

fn check_assertion(env: &InnerEnv, expr:&Exp, by:&Exp, pos: PosFromEnd) -> Result<InnerEnv,Error> {
    match by.body {
        ExpBody::Mp(a,b) => {
            if a >= env.assertions.len() {
                return Err(err(pos, format!("Modus ponens assertion index {} is out of range", a)));
            }
            if b >= env.assertions.len() {
                return Err(err(pos, format!("Modus ponens assertion index {} is out of range", b)));
            }
            let ae = env.assertions[a];
            let be = env.assertions[b];
            if ae == Exp {
                ty: Typ::Bool,

        }
    }
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
            if ae.ty != Typ::Bool {
                return Err(err(assert.0.start, format!("Expected asserted expression to have type bool, got {:?}", ae.ty)));
            }
            if be.ty != Typ::Empty {
                return Err(err(assert.0.start, format!("Expected by clause to have empty type, got {:?}", be.ty)));
            }
            let env2 = check_assertion(env, &ae, &be)?;
            let re = check_expr(env2, r)?;
            Ok(env.closure(re.ty.clone(), ExpBody::Assert(Box::new(ae), Box::new(be), Box::new(re))))
        }
        Expr::Conclude(conclude,a,mb) => {
            let ae = check_expr(env, a)?;
            let be;
            if let Some(b) = mb {
                be = check_expr(env, &b.expr)?;
            } else if env.kind == FuncKind::Axiom {
                be = env.closure(Typ::Empty, ExpBody::Primitive);
            } else {
                return Err(err(conclude.0.start, "Expected 'by' clause".to_owned()));
            }
            if ae.ty != Typ::Bool {
                return Err(err(conclude.0.start, format!("Expected asserted expression to have type bool, got {:?}", ae.ty)));
            }
            if be.ty != Typ::Empty {
                return Err(err(conclude.0.start, format!("Expected by clause to have empty type, got {:?}", be.ty)));
            }
            check_assertion(env, &ae, &be)?;
            Ok(env.closure(Typ::Empty, ExpBody::Conclude(Box::new(ae), Box::new(be))))
        }
        Expr::Mp(mp,_,a,_,b,_) => {
            let au = a.clone().n.try_into().map_err(|_|err(mp.0.start, format!("Integer overflow on {}", a)))?;
            let bu = b.clone().n.try_into().map_err(|_|err(mp.0.start, format!("Integer overflow on {}", a)))?;
            Ok(env.closure(Typ::Empty, ExpBody::Mp(au, bu)))
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
            call(env, "eq", &[&**x,&**y], o.0.start)
        }
        Expr::Imp(x,o,y) => {
            call(env, "imp", &[&**x,&**y], o.0.start)
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
        return Err(err(pos,format!("Item being called is not a function. Type is {:?}. Value is {}", fe.ty, f)));
    }
    Ok(env.closure(rett, ExpBody::Call(Box::new(fe),xes)))
}

fn create_outer_env() -> OuterEnv {
    // We write this as code simply because it's more convenient than writing out all the nodes in
    // Rust.
    let code = "
#[primitive]
fn imp(a:bool, b:bool) -> bool;

#[axiom]
fn a1(a:bool, b:bool) {
    conclude a -> b -> a
}

#[axiom]
fn a2(a:bool, b:bool, c:bool) {
    conclude (a -> b -> c) -> (a -> b) -> (a -> c)
}
";
    let module = Module::parse(code).unwrap().1;
    let mut oenv = HashMap::new();
    for f in &module.funcs {
        let (name,exp) = check_fn(&oenv, f, true).unwrap();
        oenv.insert(name, exp);
    }
    oenv
}
