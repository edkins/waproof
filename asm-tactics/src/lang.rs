#[derive(Clone,Debug,Eq,PartialEq)]
pub enum Asm {
    I32Const(u32, Tactic),
    I32Add(Tactic),
}

#[derive(Clone,Debug,Eq,PartialEq)]
pub enum Tactic {
    Positive,
    Negative,
    Fold,
    Bounds,
}
