use crate::lang::{Asm, BlockType, Expr, FullType, Func, LoopTactic, Param, Tactic, Type, VarExpr};

#[derive(Clone, Debug, Eq, PartialEq)]
enum StackItem {
    Value(VarExpr),
    Loop(usize, BlockType, usize),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct MachineFacts {
    stack: Vec<StackItem>,
    locals: Vec<VarExpr>,
    param_types: Vec<FullType>,
    hidden_types: Vec<FullType>,
    theory: Vec<Expr>,
}

impl MachineFacts {
    pub fn start_of_func(func: &Func) -> Self {
        let mut locals = vec![];

        for i in 0..func.params.len() {
            match func.params[i].typ() {
                Type::I32 => locals.push(VarExpr::i32param(i)),
            }
        }

        for local_type in &func.locals {
            match local_type {
                Type::I32 => locals.push(VarExpr::zero()),
            }
        }

        MachineFacts {
            stack: vec![],
            locals,
            param_types: func.params.clone(),
            hidden_types: func.hidden.clone(),
            theory: func.preconditions.clone(),
        }
    }

    pub fn get_param_type(&self, p: &Param) -> FullType {
        match p {
            Param::Param(i) => self.param_types[*i].clone(),
            Param::Hidden(i) => self.hidden_types[*i].clone(),
        }
    }

    pub fn fact_check(&self, e: &Expr) {
        for fact in &self.theory {
            if fact == e {
                return;
            }
        }
        panic!("Could not establish {:?}", e);
    }

    pub fn pop_value(&mut self) -> VarExpr {
        if let Some(StackItem::Value(x)) = self.stack.pop() {
            x
        } else {
            panic!("Expected value on stack");
        }
    }

    pub fn push_value(&mut self, value: VarExpr) {
        self.stack.push(StackItem::Value(value));
    }

    pub fn show_diff(&self, other: &Self) {
        let mut i = 0;
        loop {
            if i >= self.stack.len() {
                break;
            }
            if i >= other.stack.len() {
                break;
            }
            if self.stack[i] != other.stack[i] {
                break;
            }
            i += 1;
        }
        print!("    [");
        for _ in 0..i {
            print!(".");
        }
        print!("] ");
        for item in &self.stack[i..] {
            match item {
                StackItem::Value(_) => print!("-"),
                StackItem::Loop(_, _, _) => print!("|"),
            }
        }
        for item in &other.stack[i..] {
            print!(" {:?}", item);
        }
        println!();

        for i in 0..self.locals.len() {
            if self.locals[i] != other.locals[i] {
                if i < self.param_types.len() {
                    println!("    p{} = {:?}", i, other.locals[i]);
                } else {
                    println!(
                        "    l{} = {:?}",
                        i - self.param_types.len(),
                        other.locals[i]
                    );
                }
            }
        }
    }

    pub fn get_i32_base_offset(&self, expr: &VarExpr) -> (Param, VarExpr) {
        if let VarExpr::I32Linear(_, xs) = expr {
            let mut result = None;
            for (x, n) in xs {
                if self.get_param_type(x).is_address() {
                    if result.is_some() {
                        panic!("get_i32_base_offset: can't combine multiple addresses");
                    }
                    if *n != 1 {
                        panic!(
                            "get_i32_base_offset: coefficient on address must be 1, got {}",
                            n
                        );
                    }
                    result = Some(x.clone());
                }
            }

            if let Some(p) = result {
                (p.clone(), expr.i32_sub(&VarExpr::i32param_or_hidden(&p)))
            } else {
                panic!("get_i32_base_offset: no address detected");
            }
        } else {
            panic!("get_i32_base_offset: expected I32Linear");
        }
    }
}

pub fn assemble(func: &Func) {
    let mut machine = MachineFacts::start_of_func(func);
    println!("{:?}", machine);
    let mut instr_pos = 0;
    loop {
        if instr_pos >= func.body.len() {
            break;
        }
        let instr = &func.body[instr_pos];
        instr_pos += 1;
        let prev_machine = machine.clone();
        match instr {
            Asm::I32Const(n, Tactic::Default) => i32_const_default(&mut machine, *n),
            Asm::I32Add(Tactic::Default) => i32_add_default(&mut machine),
            Asm::I8Load(offset, align, Tactic::BasePlusOffset) => {
                i8_load_base_plus_offset(&mut machine, *offset, *align)
            }
            Asm::LocalGet(i, Tactic::Default) => local_get_default(&mut machine, *i),
            Asm::LocalSet(i, Tactic::Default) => local_set_default(&mut machine, *i),
            Asm::Loop(BlockType::None, Tactic::Loop(tactics)) => {
                loop_none_loop(&mut machine, instr_pos, tactics)
            }
            _ => {
                panic!("Cannot handle instr and/or tactic {:?}", instr);
            }
        }
        println!("{:?}", instr);
        prev_machine.show_diff(&machine);
    }
}

fn loop_none_loop(machine: &mut MachineFacts, instr_pos: usize, tactics: &[LoopTactic]) {
    let mut hidden_count = 0;
    for tactic in tactics {
        if let LoopTactic::Hidden(t) = tactic {
            machine.hidden_types.push(t.clone());
            hidden_count += 1;
        }
    }
    machine
        .stack
        .push(StackItem::Loop(instr_pos, BlockType::None, hidden_count));

    // TODO: check param things
}

fn i8_load_base_plus_offset(machine: &mut MachineFacts, offset: u32, align: u32) {
    if align > 0 {
        panic!("Maximum alignment for 8 bits is 2^0. Got 2^{}", align);
    }
    if offset != 0 {
        panic!("Can only currently deal with offset of 0");
    }
    let addr = machine.pop_value();
    addr.panic_unless_i32();

    let (base_param, index) = machine.get_i32_base_offset(&addr);
    if let FullType::I8Slice(len_param) = machine.get_param_type(&base_param) {
        machine.fact_check(&index.u32_lt(&len_param));
    } else {
        panic!(
            "Expected I8Slice for base, got {:?}",
            machine.get_param_type(&base_param)
        );
    }
}

fn local_get_default(machine: &mut MachineFacts, i: u32) {
    let i = i as usize;
    if i >= machine.locals.len() {
        panic!(
            "Local index out of range: {} out of {}",
            i,
            machine.locals.len()
        );
    }
    machine.push_value(machine.locals[i].clone());
}

fn local_set_default(machine: &mut MachineFacts, i: u32) {
    let i = i as usize;
    if i >= machine.locals.len() {
        panic!(
            "Local index out of range: {} out of {}",
            i,
            machine.locals.len()
        );
    }
    let a = machine.pop_value();
    if machine.locals[i].typ() == a.typ() {
        machine.locals[i] = a;
    } else {
        panic!(
            "Storing in local of incorrect type, {:?} vs {:?}",
            machine.locals[i].typ(),
            a.typ()
        );
    }
}

fn i32_const_default(machine: &mut MachineFacts, n: u32) {
    machine.push_value(VarExpr::i32const(n));
}

fn i32_add_default(machine: &mut MachineFacts) {
    let a = machine.pop_value();
    a.panic_unless_i32();
    let b = machine.pop_value();
    b.panic_unless_i32();
    machine.push_value(a.i32_add(&b));
}
