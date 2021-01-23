use lang_stuff::Span;

#[derive(Parse)]
#[symbol("#")]
pub struct Hash(pub Span);

/*
pub struct Word {
    string: String,
    span: Span,
}

pub struct Attribute {
    hash: Span,
    open: Span,
    word: Word,
    close: Span,
}

pub struct Arg {
    name: Word,
    colon: Span,
    
}

pub struct Func {
    attrs: Vec<Attribute>,
    fun: Span,
    name: Word,
    open_paren: Span,
    args: Vec<Arg>,
}
*/
