use nom::IResult;
use nom::bytes::complete::{tag,take_while};
use nom::character::complete::{multispace0,satisfy};
use nom::combinator::{recognize,value};
use nom::error::{ErrorKind, ParseError};
use nom::sequence::pair;
use std::fmt;

#[derive(Debug)]
pub struct Error {
}

impl ParseError<&str> for Error {
    fn from_error_kind(_input: &str, _kind: ErrorKind) -> Self {
        Error {}
    }
    fn append(_input: &str, _kind: ErrorKind, _other: Self) -> Self {
        Error {}
    }
}

pub trait Parse {
    fn parse(input: &str) -> IResult<&str, Self, Error> where Self:Sized;
}

pub type PosFromEnd = usize;

pub struct Span {
    pub start: PosFromEnd,
    pub end: PosFromEnd,
}

pub fn whitespace(input: &str) -> IResult<&str, (), Error> {
    value((),multispace0)(input)
}

pub fn spanned_symbol<'a>(input: &'a str, sym: &str) -> IResult<&'a str, Span, Error> {
    let (input, _) = whitespace(input)?;
    let start = input.len();
    let (input, _) = tag(sym)(input)?;
    let end = input.len();
    Ok((input,Span{start,end}))
}

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
        write!(f, "{}", &self.string)
    }
}
