use nom::IResult;
use nom::branch::alt;
use nom::bytes::complete::{tag,take_until,take_while};
use nom::character::complete::{digit1,multispace1,satisfy};
use nom::combinator::{map,opt,recognize,value};
use nom::error::{ErrorKind, ParseError};
use nom::multi::many0;
use nom::sequence::{pair,preceded};
use num_bigint::BigUint;
use std::fmt;
use std::str::FromStr;

#[derive(Debug)]
pub struct Error {
    pub msg: String,
    pub positions: Vec<PosFromEnd>,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {:?}", self.msg, self.positions)
    }
}

impl std::error::Error for Error {
}

impl ParseError<&str> for Error {
    fn from_error_kind(input: &str, kind: ErrorKind) -> Self {
        Error {
            msg: format!("{:?}", kind),
            positions: vec![input.len()]
        }
    }
    fn append(input: &str, kind: ErrorKind, mut other: Self) -> Self {
        other.msg.push_str(&format!(" {:?}", kind));
        other.positions.push(input.len());
        other
    }
}

pub trait Parse {
    fn parse(input: &str) -> IResult<&str, Self, Error> where Self:Sized;
}

pub type PosFromEnd = usize;

#[derive(Clone)]
pub struct Span {
    pub start: PosFromEnd,
    pub end: PosFromEnd,
}

fn single_line_comment(input: &str) -> IResult<&str, &str, Error> {
    preceded(tag("//"), take_until("\n"))(input)
}

pub fn whitespace(input: &str) -> IResult<&str, (), Error> {
    value((),many0(alt((multispace1,single_line_comment))))(input)
}

pub fn spanned_symbol(sym: &str) -> impl Fn(&str) -> IResult<&str, Span, Error> + '_ {
    move |input| {
        let (input, _) = whitespace(input)?;
        let start = input.len();
        let (input, _) = tag(sym)(input)?;
        let end = input.len();
        Ok((input,Span{start,end}))
    }
}

fn not_at_alphanum(input: &str) -> IResult<&str, (), Error> {
    if let Some(ch) = input.chars().next() {
        if ch.is_ascii_alphanumeric() {
            Err(nom::Err::Error(Error{
                msg: "Not_alphanumeric".to_owned(),
                positions: vec![input.len()]
            }))
        } else {
            Ok((input, ()))
        }
    } else {
        Ok((input, ()))
    }
}

pub fn spanned_keyword(keyword: &str) -> impl Fn(&str) -> IResult<&str, Span, Error> + '_ {
    move |input| {
        let (input, _) = whitespace(input)?;
        let start = input.len();
        let (input, _) = tag(keyword)(input)?;
        let (input, _) = not_at_alphanum(input)?;
        let end = input.len();
        Ok((input,Span{start,end}))
    }
}

#[derive(Clone)]
pub struct Word {
    pub string: String,
    pub span: Span,
}

fn starts_word(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}

fn continues_word(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}

impl Word {
    pub fn pos(&self) -> PosFromEnd {
        self.span.start
    }
}

impl Parse for Word {
    fn parse(input: &str) -> IResult<&str, Self, Error> {
        let (input, _) = whitespace(input)?;
        let start = input.len();
        let (input, word) = recognize(pair(satisfy(starts_word), take_while(continues_word)))(input)?;
        let end = input.len();
        Ok((input, Word{
            string: word.to_owned(),
            span: Span{start,end}
        }))
    }
}

impl fmt::Display for Word {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ", &self.string)
    }
}

impl<T:Parse> Parse for Option<T> {
    fn parse(input: &str) -> IResult<&str, Self, Error> {
        opt(T::parse)(input)
    }
}

impl<T:Parse> Parse for Vec<T> {
    fn parse(input: &str) -> IResult<&str, Self, Error> {
        many0(T::parse)(input)
    }
}

#[derive(Clone)]
pub struct Num {
    pub n: BigUint,
    pub span: Span,
}

impl Parse for Num {
    fn parse(input: &str) -> IResult<&str, Self, Error> {
        let (input, _) = whitespace(input)?;
        let start = input.len();
        let (input, num) = digit1(input)?;
        let (input, _) = not_at_alphanum(input)?;
        let end = input.len();
        Ok((input,Num{
            n: BigUint::from_str(num).unwrap(),
            span: Span{start,end}
        }))
    }
}

impl fmt::Display for Num {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} ", &self.n)
    }
}

impl<T:Parse> Parse for Box<T> {
    fn parse(input: &str) -> IResult<&str, Self, Error> {
        map(T::parse, Box::new)(input)
    }
}

impl From<Error> for std::io::Error {
    fn from(e: Error) -> Self {
        std::io::Error::new(std::io::ErrorKind::Other, e)
    }
}
