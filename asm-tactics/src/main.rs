use crate::lang::{Asm,Expr,Func,FullType,Param,Type,Tactic};

mod assembler;
mod lang;

fn main() {
    let func = Func {
        params: vec![
            FullType::I8Slice(Param::Hidden(0)),
            FullType::I32,
        ],
        result: Some(FullType::I32),
        locals: vec![],
        hidden: vec![
            FullType::I32,
        ],
        preconditions: vec![
            Expr::Const(0).le(Param::Param(1).expr()),
            Param::Param(1).expr().lt(Param::Hidden(0).expr()),
        ],
        body: vec![
            Asm::LocalGet(1, Tactic::Default),
            Asm::LocalGet(0, Tactic::Default),
            Asm::I32Add(Tactic::Default),
            Asm::I8Load(0, 0, Tactic::BasePlusOffset),
        ]
    };
    assembler::assemble(&func);
}