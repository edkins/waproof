use lang_stuff::{Span,Word};

#[derive(Parse)]
#[symbol("#")]
pub struct Hash(pub Span);

#[derive(Parse)]
#[symbol("[")]
pub struct OpenSquare(pub Span);

#[derive(Parse)]
#[symbol("]")]
pub struct ClosedSquare(pub Span);

#[derive(Parse)]
#[symbol("(")]
pub struct OpenParen(pub Span);

#[derive(Parse)]
#[symbol(")")]
pub struct ClosedParen(pub Span);

#[derive(Parse)]
#[symbol("{")]
pub struct OpenBrace(pub Span);

#[derive(Parse)]
#[symbol("}")]
pub struct ClosedBrace(pub Span);

#[derive(Parse)]
#[symbol(":")]
pub struct Colon(pub Span);

#[derive(Parse)]
#[symbol(",")]
pub struct Comma(pub Span);

#[derive(Parse)]
#[symbol("->")]
pub struct Arrow(pub Span);

#[derive(Parse)]
#[symbol(";")]
pub struct Semicolon(pub Span);

#[derive(Parse)]
pub struct Attribute {
    pub hash: Hash,
    pub open: OpenSquare,
    pub word: Word,
    pub close: ClosedSquare,
}

#[derive(Parse)]
pub enum Type {
    #[keyword("N")]
    Nat(Span),
    #[keyword("bool")]
    Bool(Span),
}

#[derive(Parse)]
pub struct Arg {
    name: Word,
    colon: Colon,
    ty: Type,
    comma: Option<Comma>,
}

#[derive(Parse)]
#[keyword("fn")]
pub struct Fun(pub Span);

#[derive(Parse)]
pub struct ReturnType {
    arrow: Arrow,
    ty: Type,
}

#[derive(Parse)]
pub enum FuncBodyOpt {
    Semicolon(Semicolon),
    Body(FuncBody),
}

#[derive(Parse)]
pub struct FuncBody {
    open: OpenBrace,
    close: ClosedBrace,
}

#[derive(Parse)]
pub struct Func {
    attrs: Vec<Attribute>,
    fun: Fun,
    name: Word,
    open: OpenParen,
    args: Vec<Arg>,
    close: ClosedParen,
    ret: Option<ReturnType>,
    body: FuncBodyOpt,
}
