use crate::lang::{Asm,Tactic};

mod assembler;
mod lang;

fn main() {
    let code = [
        Asm::I32Const(2, Tactic::Positive),
        Asm::I32Const(2, Tactic::Positive),
        Asm::I32Add(Tactic::Fold),
    ];
    assembler::assemble(&code);
}
