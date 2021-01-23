use nom::IResult;
use nom::bytes::complete::tag;
use nom::character::complete::multispace0;
use nom::combinator::value;
use nom::error::{ErrorKind, ParseError};

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
