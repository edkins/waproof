use lang_stuff::{Delimited,Delimited1,Error,Num,Parse,Span,Word,whitespace};
use nom::{IResult,combinator::{all_consuming,map}, sequence::{terminated,tuple}};

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
#[symbol("[")]
pub struct LSquare(pub Span);

#[derive(Clone,Parse)]
#[symbol("]")]
pub struct RSquare(pub Span);

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
#[symbol("=>")]
pub struct DoubleArrow(pub Span);

#[derive(Clone,Parse)]
pub enum Expr {
    Num(Num),
    Call(Word, LParen, Delimited<Expr,Comma>, RParen),
    Word(Word),
    HashWord(Hash, Word),
    List(LSquare, Delimited<Expr,Comma>, RSquare),
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
    pub statements: Vec<Statement>,
}

impl Parse for Module {
    fn parse(input: &str) -> IResult<&str, Self, Error> {
        map(all_consuming(terminated(Vec::<Statement>::parse, whitespace)), |statements|Module{statements})(input)
    }
}

#[derive(Clone,ParseDisplay)]
pub struct Expansion {
    pub left: Expr,
    pub arrow: DoubleArrow,
    pub right: Expr,
}

impl Parse for Expansion {
    fn parse(input: &str) -> IResult<&str, Self, Error> {
        map(all_consuming(terminated(tuple((Expr::parse,DoubleArrow::parse,Expr::parse)), whitespace)), |(left,arrow,right)|Expansion{left,arrow,right})(input)
    }
}
