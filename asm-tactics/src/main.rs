use crate::lang::{Asm, BlockType, FullType, Func, LoopTactic, Tactic, VarExpr};
use clap::clap_app;

mod assembler;
mod lang;

fn main() {
    let matches = clap_app!(asm_tactics =>
    (@arg TEST: +required "Name of test to run")
    )
    .get_matches();
    let test = matches.value_of("TEST").unwrap();
    match test {
        "slice_get" => slice_get(),
        "reverse" => reverse(),
        _ => panic!(),
    }
}

#[test]
fn tests() {
    slice_get();
    reverse();
}

fn reverse() {
    let func = Func {
        params: vec![FullType::I8Slice(VarExpr::i32param(1)), FullType::I32],
        result: None,
        locals: vec![],
        hidden: vec![],
        preconditions: vec![],
        body: vec![
            Asm::LocalGet(0, Tactic::Default),
            Asm::LocalGet(1, Tactic::Default),
            Asm::I32Add(Tactic::Default),
            Asm::LocalSet(1, Tactic::Default),
            Asm::Loop(
                BlockType::None,
                Tactic::Loop(vec![
                    LoopTactic::Hidden(VarExpr::zero()),
                    LoopTactic::Local(0, VarExpr::i32param(0).i32_add(&VarExpr::i32hidden(0))),
                    LoopTactic::Local(
                        1,
                        VarExpr::i32param(0)
                            .i32_add(&VarExpr::i32param(1).i32_sub(&VarExpr::i32hidden(0))),
                    ),
                ]),
            ),
            Asm::LocalGet(1, Tactic::Default),
            Asm::LocalGet(0, Tactic::Default),
            Asm::I32Leu(Tactic::Default),
            Asm::BrIf(1, Tactic::Default),

            Asm::LocalGet(1, Tactic::Default),
            Asm::I32Const(1, Tactic::Default),
            Asm::I32Sub(Tactic::Default),
            Asm::LocalTee(1, Tactic::Default),

            Asm::LocalGet(0, Tactic::Default),
            Asm::I8Load(0, 0, Tactic::BasePlusOffset),
        ],
    };
    assembler::assemble(&func);
}

fn slice_get() {
    let func = Func {
        params: vec![FullType::I8Slice(VarExpr::i32hidden(0)), FullType::I32],
        result: Some(FullType::I32),
        locals: vec![],
        hidden: vec![FullType::I32],
        preconditions: vec![VarExpr::i32param(1).i32_ltu(&VarExpr::i32hidden(0))],
        body: vec![
            Asm::LocalGet(1, Tactic::Default),
            Asm::LocalGet(0, Tactic::Default),
            Asm::I32Add(Tactic::Default),
            Asm::I8Load(0, 0, Tactic::BasePlusOffset),
        ],
    };
    assembler::assemble(&func);
}
