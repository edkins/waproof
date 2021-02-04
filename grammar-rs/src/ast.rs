use lang_stuff::{Delimited,Delimited1,Error,Num,Parse,Span,Word,whitespace};
use nom::{IResult,combinator::{all_consuming,map}, sequence::terminated};

#[derive(Clone,Parse)]
#[symbol(".")]
pub struct Dot(pub Span);

#[derive(Clone,Parse)]
#[symbol("#")]
pub struct Hash(pub Span);

#[derive(Clone,Parse)]
#[symbol("(")]
pub struct LParen(pub Span);

#[derive(Clone,Parse)]
#[symbol(")")]
pub struct RParen(pub Span);

#[derive(Clone,Parse)]
#[symbol(",")]
pub struct Comma(pub Span);

#[derive(Clone,Parse)]
#[symbol("|")]
pub struct Bar(pub Span);

#[derive(Clone,Parse)]
#[symbol("::=")]
pub struct Expands(pub Span);

#[derive(Clone,Parse)]
pub enum Expr {
    Num(Num),
    Call(Word, LParen, Delimited<Expr,Comma>, RParen),
    Word(Word),
    HashWord(Hash, Word),
    Tuple(LParen, Delimited<Expr,Comma>, RParen),
}

#[derive(Clone,Parse)]
pub enum Definition {
    Exprs(Delimited1<Expr,Bar>),
    JustHash(Hash),
}

#[derive(Clone,Parse)]
pub enum Statement {
    Expand(Delimited1<Expr,Comma>, Expands, Definition, Dot),
}

#[derive(Clone,ParseDisplay)]
pub struct Module {
    pub funcs: Vec<Statement>,
}

impl Parse for Module {
    fn parse(input: &str) -> IResult<&str, Self, Error> {
        map(all_consuming(terminated(Vec::<Statement>::parse, whitespace)), |funcs|Module{funcs})(input)
    }
}
