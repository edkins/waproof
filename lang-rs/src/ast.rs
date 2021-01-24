use lang_stuff::{Error,Num,Parse,Span,Word,whitespace};
use nom::IResult;
use nom::branch::alt;
use nom::combinator::{map,success,all_consuming,opt};
use nom::sequence::{terminated,tuple};

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

#[derive(Clone,Parse)]
pub struct CallArg {
    expr: Expr,
    comma: Option<Comma>,
}

#[derive(Clone,Parse)]
#[keyword("assert")]
pub struct Assert(pub Span);

#[derive(Clone,Parse)]
#[keyword("by")]
pub struct By(pub Span);

#[derive(Clone,Parse)]
#[keyword("conclude")]
pub struct Conclude(pub Span);

#[derive(Clone,Parse)]
pub struct ByClause {
    by: By,
    expr: Box<Expr>,
}

#[derive(Clone,ParseDisplay)]
pub enum Expr {
    Num(Num),
    Assert(Assert,Box<Expr>,Option<ByClause>,Semicolon,Box<Expr>),
    Conclude(Conclude,Box<Expr>,Option<ByClause>),
    Call(Word,OpenParen,Vec<CallArg>,ClosedParen),
    Var(Word),
    Paren(OpenParen,Box<Expr>,ClosedParen),
    Eq(Box<Expr>,Equals,Box<Expr>),
    Imp(Box<Expr>,Arrow,Box<Expr>),
}

fn parse_expr(max_level: usize) -> impl Fn(&str) -> IResult<&str, Expr, Error> {
    move |input| {
        let (input,r) = alt((
            map(Num::parse, Expr::Num),
            map(tuple((Assert::parse, parse_expr(0), opt(tuple((By::parse,parse_expr(0)))), Semicolon::parse, parse_expr(0))), |(a,e,b,s,x)|Expr::Assert(a,Box::new(e),b.map(|(by,be)|ByClause{by,expr:Box::new(be)}),s,Box::new(x))),
            map(tuple((Conclude::parse, parse_expr(0), opt(tuple((By::parse,parse_expr(0)))))), |(c,e,b)|Expr::Conclude(c,Box::new(e),b.map(|(by,be)|ByClause{by,expr:Box::new(be)}))),
            map(tuple((Word::parse, OpenParen::parse, Vec::<CallArg>::parse, ClosedParen::parse)), |(f,o,a,c)|Expr::Call(f,o,a,c)),
            map(Word::parse, Expr::Var),
            map(tuple((OpenParen::parse, parse_expr(0), ClosedParen::parse)), |(o,e,c)|Expr::Paren(o,Box::new(e),c)),
        ))(input)?;

        if max_level > 1 {
            return Ok((input,r));
        }

        let (input,r) = alt((
            map(tuple((Equals::parse, parse_expr(2))), |(op,e)|Expr::Eq(Box::new(r.clone()),op,Box::new(e))),
            success(r.clone())
        ))(input)?;

        if max_level > 0 {
            return Ok((input,r));
        }

        let (input,r) = alt((
            map(tuple((Arrow::parse, parse_expr(0))), |(op,e)|Expr::Imp(Box::new(r.clone()),op,Box::new(e))),
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

#[derive(Clone,ParseDisplay)]
pub struct Module {
    funcs: Vec<Func>,
}

impl Parse for Module {
    fn parse(input: &str) -> IResult<&str, Self, Error> {
        map(all_consuming(terminated(Vec::<Func>::parse, whitespace)), |funcs|Module{funcs})(input)
    }
}
