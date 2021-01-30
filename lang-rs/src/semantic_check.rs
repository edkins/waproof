use std::collections::HashMap;
use std::convert::TryInto;
use lang_stuff::{Error,Parse,PosFromEnd};
use crate::ast::{Arg,Expr,Func,FuncBodyOpt,Module,Type};
use crate::semantic::{CallHead,Exp,ExpBody,OuterEnv,OEnvThing,TheoremSchema,Typ};

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

#[derive(Clone)]
struct InnerEnv {
    outer: OuterEnv,
    params: HashMap<String,Typ>,
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
    fn from_outer(outer: &OuterEnv, kind: FuncKind, args: &[Arg]) -> Result<Self,Error> {
        let mut params = HashMap::new();
        for arg in args {
            if params.contains_key(&arg.name.string) {
                return Err(err(arg.name.pos(),format!("Duplicate parameter name {}", arg.name.string)));
            }
            if outer.contains_key(&arg.name.string) {
                return Err(err(arg.name.pos(),format!("Parameter name is already used in outer env: {}", arg.name.string)));
            }
            params.insert(arg.name.string.clone(), arg.ty.to_typ());
        }
        Ok(InnerEnv {
            outer: outer.clone(),
            params,
            inner: HashMap::new(),
            typs: vec![],
            kind,
            assertions: vec![],
        })
    }
    fn lookup_call_head(&self, string: &str, pos: PosFromEnd) -> Result<(Typ,CallHead),Error> {
        if let Some(e) = self.outer.get(string) {
            Ok((e.ty.clone(), CallHead::Const(string.to_owned())))
        } else if let Some(t) = self.params.get(string) {
            Ok((t.clone(), CallHead::Param(string.to_owned())))
        } else {
            Err(err(pos,format!("Name {} is not defined or cannot be called", string)))
        }
    }
    fn lookup_expr(&self, string: &str, pos: PosFromEnd) -> Result<Exp,Error> {
        if let Some(i) = self.inner.get(string) {
            Ok(self.closure(self.typs[*i].clone(), ExpBody::Var(*i)))
        } else if let Ok((t,c)) = self.lookup_call_head(string, pos) {
            Ok(self.closure(t, ExpBody::Const(c)))
        } else {
            Err(err(pos,format!("Name {} is not defined", string)))
        }
    }
    fn lookup_theorem_schema(&self, name: &str, pos: PosFromEnd) -> Result<TheoremSchema,Error> {
        if let Some(oe) = self.outer.get(name) {
            if let Some(t) = &oe.theorem {
                Ok(t.clone())
            } else {
                Err(err(pos,format!("Name {:?} is not a theorem", name)))
            }
        } else {
            Err(err(pos,format!("Name {:?} is not defined in outer environment", name)))
        }
    }
    fn closure(&self, ty: Typ, body: ExpBody) -> Exp {
        Exp{ty, body, free_vars: self.typs.clone()}
    }
    fn with_assertion(&self, expr: &Exp) -> Self {
        let mut result = self.clone();
        result.assertions.push(expr.clone());
        result
    }
}

impl Exp {
    fn get_conclusion(&self, pos: PosFromEnd) -> Result<Exp,Error> {
        match &self.body {
            ExpBody::Assert(_,_,e) => e.get_conclusion(pos),
            ExpBody::Conclude(c,_) => Ok((**c).clone()),
            _ => Err(err(pos,format!("Expression {} does not have conclusion", self)))
        }
    }
    fn subst_params(&self, substs: &HashMap<String,Exp>, pos: PosFromEnd) -> Result<Exp,Error> {
        match &self.body {
            ExpBody::Var(_) => Ok(self.clone()),
            ExpBody::Const(CallHead::Param(c)) => Ok(substs.get(c).unwrap().clone()),  // type checking should have ensured existence
            ExpBody::Call(CallHead::Param(f), args) => {
                //let args2 = args.iter().map(|a|a.subst_params(substs, pos)?).collect();
                panic!();  // TODO
            }
            ExpBody::Call(CallHead::Const(c), args) => {
                let args2:Vec<_> = args.iter().map(|a|a.subst_params(substs, pos)).collect::<Result<_,_>>()?;
                Ok(Exp{
                    ty: self.ty.clone(),
                    free_vars: self.free_vars.clone(),
                    body:ExpBody::Call(CallHead::Const(c.to_owned()), args2)
                })
            }
            _ => panic!("Not expecting this expression type here: {}", self)
        }
    }
}

pub fn check_module(m: &Module) -> Result<(),Error> {
    let mut oenv = create_outer_env();
    for f in &m.funcs {
        let (name,ty,theorem) = check_fn(&oenv, f, false)?;
        oenv.insert(name, OEnvThing{ty,theorem});
    }
    Ok(())
}

fn check_fn(oenv: &OuterEnv, f: &Func, allow_axioms: bool) -> Result<(String,Typ,Option<TheoremSchema>),Error> {
    let kind = check_fn_attributes(f, allow_axioms)?;
    let lenv = InnerEnv::from_outer(oenv, kind.clone(), &f.args)?;
    let params:Vec<_> = f.args.iter().map(|a|(a.name.string.clone(),a.ty.to_typ())).collect();
    let rett = f.ret.as_ref().map(|r|r.ty.to_typ()).unwrap_or(Typ::Empty);
    let param_types:Vec<_> = params.iter().map(|p|p.1.clone()).collect();
    let fty = Typ::Func(param_types,Box::new(rett.clone()));

    if oenv.contains_key(&f.name.string) {
        return Err(err(f.name.pos(),format!("Function name {} is already used in outer env", f.name.string)));
    }

    let theorem = match (&f.body, &kind) {
        (FuncBodyOpt::Body(b), FuncKind::Theorem) |
        (FuncBodyOpt::Body(b), FuncKind::Axiom) => {
            let be = check_expr(&lenv, &b.expr)?;
            if be.ty != rett {
                return Err(err(b.open.0.start, format!("Declared return type is {:?}, actual return type is {:?}", rett, be.ty)));
            }
            if !be.free_vars.is_empty() {
                return Err(err(b.open.0.start, "Not expecting free vars here".to_owned()));
            }
            let conc = be.get_conclusion(f.name.pos())?;
            Some(TheoremSchema{params, conc})
        }
        (FuncBodyOpt::Body(b), _) => {
            return Err(err(b.open.0.start, "Expected no function body".to_owned()));
        }
        (FuncBodyOpt::Semicolon(_), FuncKind::Primitive) => {None}
        (FuncBodyOpt::Semicolon(s), _) => {
            return Err(err(s.0.start, "Expected function body".to_owned()));
        }
    };

    Ok((f.name.string.clone(),fty,theorem))
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
    match &by.body {
        ExpBody::Mp(a,b) => {
            if *a >= env.assertions.len() {
                return Err(err(pos, format!("Modus ponens assertion index {} is out of range", a)));
            }
            if *b >= env.assertions.len() {
                return Err(err(pos, format!("Modus ponens assertion index {} is out of range", b)));
            }
            let ae = &env.assertions[*a];
            let be = &env.assertions[*b];
            let expected = Exp {
                ty: Typ::Bool,
                free_vars: vec![],
                body: ExpBody::Call(CallHead::Const("imp".to_owned()), vec![be.clone(),expr.clone()])
            };
            if *ae == expected {
                Ok(env.with_assertion(expr))
            } else {
                Err(err(pos, format!("Modus ponens mismatch:\nExpected {}\nGot      {}", expected, ae)))
            }
        }
        ExpBody::Call(CallHead::Const(name), args) => {
            let theorem = env.lookup_theorem_schema(&name, pos)?;
            
            // This shouldn't happen? Already type checked.
            if theorem.params.len() != args.len() {
                return Err(err(pos, format!("Theorem takes {} parameters. {} were supplied", theorem.params.len(), args.len())));
            }

            let mut substs = HashMap::new();
            for i in 0..theorem.params.len() {
                substs.insert(theorem.params[i].0.clone(), args[i].clone());
            }
            let conc = theorem.conc.subst_params(&substs, pos)?;
            if *expr == conc {
                Ok(env.with_assertion(expr))
            } else {
                Err(err(pos, "Wrong conclusion".to_owned()))
            }
        }
        _ => Err(err(pos, format!("Expression {} is not a theorem reference", by)))
    }
}

fn check_expr(env: &InnerEnv, main_expr:&Expr) -> Result<Exp,Error> {
    match main_expr {
        Expr::Num(n) => {
            Ok(env.closure(Typ::Nat, ExpBody::Const(CallHead::Num(n.n.clone()))))
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
            let env2 = check_assertion(env, &ae, &be, assert.0.start)?;
            let re = check_expr(&env2, r)?;
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
            // Axioms can assert whatever they like
            if env.kind != FuncKind::Axiom {
                check_assertion(env, &ae, &be, conclude.0.start)?;
            }
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
            env.lookup_expr(&x.string, x.pos())
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
    let (ft,fe) = env.lookup_call_head(f, pos)?;
    let xes = xs.iter().map(|x|check_expr(env,x)).collect::<Result<Vec<_>,Error>>()?;
    if let Typ::Func(ats, rt) = &ft {
        if ats.len() != xes.len() {
            return Err(err(pos,format!("Expected function {} to be called with {} arguments, got {}", f, ats.len(), xes.len())));
        }
        for i in 0..ats.len() {
            if xes[i].ty != ats[i] {
                return Err(err(pos,format!("Expected argument {} to be of type {:?}, got {:?}", i, ats[i], xes[i].ty)));
            }
        }
        rett = *rt.clone();
    } else {
        return Err(err(pos,format!("Item being called is not a function. Type is {:?}. Value is {}", ft, f)));
    }
    Ok(env.closure(rett, ExpBody::Call(fe,xes)))
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
        let (name,ty,theorem) = check_fn(&oenv, f, true).unwrap();
        println!("Added {} {:?}", name, ty);
        oenv.insert(name, OEnvThing{ty,theorem});
    }
    oenv
}
