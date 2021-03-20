use crate::lang::{Asm,Tactic};

#[derive(Clone,Debug,Eq,PartialEq)]
enum StackItem {
    U32(u32),
}

pub fn assemble(code: &[Asm]) {
    let mut stack = vec![];
    for instr in code {
        match instr {
            Asm::I32Const(n, Tactic::Positive) => i32_const_positive(&mut stack, *n),
            Asm::I32Add(Tactic::Fold) => i32_add_fold(&mut stack),
            _ => {
                panic!("Cannot handle instr and/or tactic {:?}", instr);
            }
        }
        println!("{:?} -- {:?}", instr, stack);
    }
}

fn i32_const_positive(stack: &mut Vec<StackItem>, n: u32) {
    stack.push(StackItem::U32(n));
}

fn i32_add_fold(stack: &mut Vec<StackItem>) {
    if let Some(StackItem::U32(a)) = stack.pop() {
        if let Some(StackItem::U32(b)) = stack.pop() {
            if let Some(c) = a.checked_add(b) {
                stack.push(StackItem::U32(c));
                return;
            } else {
                panic!("Overflow in fold");
            }
        }
    }
    panic!("Expected two U32 consts");
}
