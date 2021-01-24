use lang_stuff::{Error,Num,Parse,Span,Word};
use nom::IResult;
use nom::branch::alt;
use nom::combinator::{map,success};
use nom::sequence::tuple;

#[derive(Clone,Parse)]
#[symbol("#")]
pub struct Hash(pub Span);

#[derive(Clone,Parse)]
#[symbol("[")]
pub struct OpenSquare(pub Span);

#[derive(Clone,Parse)]
#[symbol("]")]
pub struct ClosedSquare(pub Span);

#[derive(Clone,Parse)]
#[symbol("(")]
pub struct OpenParen(pub Span);

#[derive(Clone,Parse)]
#[symbol(")")]
pub struct ClosedParen(pub Span);

#[derive(Clone,Parse)]
#[symbol("{")]
pub struct OpenBrace(pub Span);

#[derive(Clone,Parse)]
#[symbol("}")]
pub struct ClosedBrace(pub Span);

#[derive(Clone,Parse)]
#[symbol(":")]
pub struct Colon(pub Span);

#[derive(Clone,Parse)]
#[symbol(",")]
pub struct Comma(pub Span);

#[derive(Clone,Parse)]
#[symbol("->")]
pub struct Arrow(pub Span);

#[derive(Clone,Parse)]
#[symbol(";")]
pub struct Semicolon(pub Span);

#[derive(Clone,Parse)]
#[symbol("==")]
pub struct Equals(pub Span);

#[derive(Clone,Parse)]
pub struct Attribute {
    pub hash: Hash,
    pub open: OpenSquare,
    pub word: Word,
    pub close: ClosedSquare,
}

#[derive(Clone,Parse)]
pub enum Type {
    #[keyword("N")]
    Nat(Span),
    #[keyword("bool")]
    Bool(Span),
}

#[derive(Clone,Parse)]
pub struct Arg {
    name: Word,
    colon: Colon,
    ty: Type,
    comma: Option<Comma>,
}

#[derive(Clone,Parse)]
#[keyword("fn")]
pub struct Fun(pub Span);

#[derive(Clone,Parse)]
pub struct ReturnType {
    arrow: Arrow,
    ty: Type,
}

#[derive(Clone,Parse)]
pub enum FuncBodyOpt {
    Semicolon(Semicolon),
    Body(FuncBody),
}

#[derive(Clone,Parse)]
pub struct FuncBody {
    open: OpenBrace,
    expr: Expr,
    close: ClosedBrace,
}

#[derive(Clone,Parse)]
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

#[derive(Clone,ParseDisplay)]
pub enum Expr {
    Num(Num),
    Var(Word),
    Paren(OpenParen,Box<Expr>,ClosedParen),
    Eq(Box<Expr>,Equals,Box<Expr>),
}

fn parse_expr(max_level: usize) -> impl Fn(&str) -> IResult<&str, Expr, Error> {
    move |input| {
        let (input,r) = alt((
            map(Num::parse, Expr::Num),
            map(Word::parse, Expr::Var),
            map(tuple((OpenParen::parse, parse_expr(0), ClosedParen::parse)), |(o,e,c)|Expr::Paren(o,Box::new(e),c)),
        ))(input)?;

        if max_level > 0 {
            return Ok((input,r));
        }

        let (input,r) = alt((
            map(tuple((Equals::parse, parse_expr(1))), |(op,e)|Expr::Eq(Box::new(r.clone()),op,Box::new(e))),
            success(r.clone())
        ))(input)?;

        Ok((input,r))
    }
}

impl Parse for Expr {
    fn parse(input: &str) -> IResult<&str, Self, Error> {
        parse_expr(0)(input)
    }
}

