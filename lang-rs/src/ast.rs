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
pub struct Attribute {
    pub hash: Hash,
    pub open: OpenSquare,
    pub word: Word,
    pub close: ClosedSquare,
}

/*
#[derive(Parse)]
pub struct Arg {
    name: Word,
    colon: Span,
    ty: Type,
}

pub struct Func {
    attrs: Vec<Attribute>,
    fun: Span,
    name: Word,
    open_paren: Span,
    args: Vec<Arg>,
}
*/
