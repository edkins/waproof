use crate::pa_axiom::Theorem;
use crate::pa_convenience::num;
use crate::pa_formula::{Expr, Formula, SyntaxError};
use nom::branch::alt;
use nom::bytes::complete::{tag, take_while};
use nom::character::complete::{digit1, multispace0, satisfy};
use nom::combinator::{all_consuming, opt, recognize, value};
use nom::error::ErrorKind;
use nom::sequence::{delimited, pair, preceded, terminated};
use nom::IResult;
use std::fmt::Debug;
use std::rc::Rc;
use std::str::FromStr;

#[derive(Debug)]
pub enum ParseError {
    Nom(ErrorKind, usize),
    Check(String),
    Syntax(SyntaxError),
    NotAlphanumeric,
    NumberTooBig,
    Incomplete,
}

impl nom::error::ParseError<&str> for ParseError {
    fn from_error_kind(input: &str, kind: ErrorKind) -> Self {
        ParseError::Nom(kind, input.len())
    }
    fn append(_input: &str, _kind: ErrorKind, other: Self) -> Self {
        other
    }
}

impl From<SyntaxError> for ParseError {
    fn from(e: SyntaxError) -> Self {
        ParseError::Syntax(e)
    }
}

pub fn syn(e: SyntaxError) -> nom::Err<ParseError> {
    nom::Err::Error(ParseError::Syntax(e))
}

pub fn extract_parse_error(e: nom::Err<ParseError>) -> ParseError {
    match e {
        nom::Err::Incomplete(_) => ParseError::Incomplete,
        nom::Err::Error(e) | nom::Err::Failure(e) => e,
    }
}

fn starts_word(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}

fn continues_word(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}

fn not_at_alphanum(input: &str) -> IResult<&str, (), ParseError> {
    if let Some(ch) = input.chars().next() {
        if ch.is_ascii_alphanumeric() {
            Err(nom::Err::Error(ParseError::NotAlphanumeric))
        } else {
            Ok((input, ()))
        }
    } else {
        Ok((input, ()))
    }
}

pub fn parse_sym(sym: &'static str) -> impl Fn(&str) -> IResult<&str, (), ParseError> {
    move |input| {
        let (input, _) = multispace0(input)?;
        let (input, _) = tag(sym)(input)?;
        Ok((input, ()))
    }
}

pub fn parse_keyword(sym: &'static str) -> impl Fn(&str) -> IResult<&str, (), ParseError> {
    move |input| {
        let (input, _) = multispace0(input)?;
        let (input, _) = tag(sym)(input)?;
        let (input, _) = not_at_alphanum(input)?;
        Ok((input, ()))
    }
}

pub fn parse_var_str(input: &str) -> IResult<&str, &str, ParseError> {
    let (input, _) = multispace0(input)?;
    let (input, word) = recognize(pair(satisfy(starts_word), take_while(continues_word)))(input)?;
    Ok((input, word))
}

fn parse_var(input: &str) -> IResult<&str, Expr, ParseError> {
    let (input, x) = parse_var_str(input)?;
    Ok((input, Expr::var(x)))
}

fn parse_number(input: &str) -> IResult<&str, Expr, ParseError> {
    let (input, _) = multispace0(input)?;
    let (input, number) = digit1(input)?;
    let (input, _) = not_at_alphanum(input)?;
    let n = number
        .parse()
        .map_err(|_| nom::Err::Error(ParseError::NumberTooBig))?;
    Ok((input, num(n)))
}

fn parse_s(input: &str) -> IResult<&str, Expr, ParseError> {
    let (input, _) = parse_keyword("S")(input)?;
    let (input, _) = parse_sym("(")(input)?;
    let (input, e) = parse_expr(input)?;
    let (input, _) = parse_sym(")")(input)?;
    Ok((input, e.s()))
}

fn parse_paren(input: &str) -> IResult<&str, Expr, ParseError> {
    delimited(parse_sym("("), parse_expr, parse_sym(")"))(input)
}

fn parse_term(input: &str) -> IResult<&str, Expr, ParseError> {
    alt((parse_paren, parse_s, parse_number, parse_var))(input)
}

fn parse_muls(input: &str) -> IResult<&str, Expr, ParseError> {
    let (input, a) = parse_term(input)?;
    let (input, mb) = opt(preceded(parse_sym("*"), parse_muls))(input)?;
    let r = match mb {
        None => a,
        Some(b) => a * b,
    };
    Ok((input, r))
}

pub fn parse_expr(input: &str) -> IResult<&str, Expr, ParseError> {
    let (input, a) = parse_muls(input)?;
    let (input, mb) = opt(preceded(parse_sym("+"), parse_expr))(input)?;
    let r = match mb {
        None => a,
        Some(b) => a + b,
    };
    Ok((input, r))
}

impl FromStr for Expr {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(all_consuming(terminated(parse_expr, multispace0))(s)
            .map_err(extract_parse_error)?
            .1)
    }
}

fn parse_false(input: &str) -> IResult<&str, Formula, ParseError> {
    value(Formula::falsehood(), parse_keyword("false"))(input)
}

fn parse_eq(input: &str) -> IResult<&str, Formula, ParseError> {
    let (input, a) = parse_expr(input)?;
    let (input, _) = parse_sym("=")(input)?;
    let (input, b) = parse_expr(input)?;
    Ok((input, a.eq(b)))
}

fn parse_paren_formula(input: &str) -> IResult<&str, Formula, ParseError> {
    delimited(parse_sym("("), parse_formula, parse_sym(")"))(input)
}

fn parse_not(input: &str) -> IResult<&str, Formula, ParseError> {
    let (input, f) = preceded(parse_sym("!"), parse_tight)(input)?;
    Ok((input, !f))
}

fn parse_forall(input: &str) -> IResult<&str, Formula, ParseError> {
    let (input, _) = parse_sym("@")(input)?;
    let (input, x) = parse_var_str(input)?;
    let (input, f) = delimited(parse_sym("("), parse_formula, parse_sym(")"))(input)?;
    Ok((input, f.forall(x).map_err(syn)?))
}

fn parse_exists(input: &str) -> IResult<&str, Formula, ParseError> {
    let (input, _) = parse_sym("#")(input)?;
    let (input, x) = parse_var_str(input)?;
    let (input, f) = delimited(parse_sym("("), parse_formula, parse_sym(")"))(input)?;
    Ok((input, f.exists(x).map_err(syn)?))
}

fn parse_tight(input: &str) -> IResult<&str, Formula, ParseError> {
    alt((
        parse_paren_formula,
        parse_false,
        parse_forall,
        parse_exists,
        parse_not,
        parse_eq,
    ))(input)
}

fn parse_imps(input: &str) -> IResult<&str, Formula, ParseError> {
    let (input, a) = parse_tight(input)?;
    let (input, mb) = opt(preceded(parse_sym("->"), parse_imps))(input)?;
    let r = match mb {
        None => a,
        Some(b) => a.imp(b).map_err(syn)?,
    };
    Ok((input, r))
}

fn parse_ands(input: &str) -> IResult<&str, Formula, ParseError> {
    let (input, a) = parse_imps(input)?;
    let (input, mb) = opt(preceded(parse_sym("&"), parse_ands))(input)?;
    let r = match mb {
        None => a,
        Some(b) => a.and(b).map_err(syn)?,
    };
    Ok((input, r))
}

pub fn parse_formula(input: &str) -> IResult<&str, Formula, ParseError> {
    let (input, a) = parse_ands(input)?;
    let (input, mb) = opt(preceded(parse_sym("|"), parse_formula))(input)?;
    let r = match mb {
        None => a,
        Some(b) => a.or(b).map_err(syn)?,
    };
    Ok((input, r))
}

impl FromStr for Formula {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let result = all_consuming(terminated(parse_formula, multispace0))(s)
            .map_err(extract_parse_error)?
            .1;
        Ok(result)
    }
}

pub trait ToFormula {
    fn into_formula(self) -> Result<Formula, ParseError>;
}

impl ToFormula for Formula {
    fn into_formula(self) -> Result<Formula, ParseError> {
        Ok(self)
    }
}

impl ToFormula for &Formula {
    fn into_formula(self) -> Result<Formula, ParseError> {
        Ok(self.clone())
    }
}

impl ToFormula for &str {
    fn into_formula(self) -> Result<Formula, ParseError> {
        self.parse()
    }
}

impl ToFormula for &Rc<Formula> {
    fn into_formula(self) -> Result<Formula, ParseError> {
        Ok((**self).clone())
    }
}

pub trait ToExpr {
    fn into_expr(self) -> Result<Expr, ParseError>;
}

impl ToExpr for Expr {
    fn into_expr(self) -> Result<Expr, ParseError> {
        Ok(self)
    }
}

impl ToExpr for &Expr {
    fn into_expr(self) -> Result<Expr, ParseError> {
        Ok(self.clone())
    }
}

impl ToExpr for &str {
    fn into_expr(self) -> Result<Expr, ParseError> {
        self.parse()
    }
}

impl ToExpr for &Rc<Expr> {
    fn into_expr(self) -> Result<Expr, ParseError> {
        Ok((**self).clone())
    }
}

impl Theorem {
    pub fn checkr(&self, parseable: impl ToFormula + Clone + Debug) -> Result<(), ParseError> {
        if parseable.clone().into_formula()? == *self.formula() {
            Ok(())
        } else {
            Err(ParseError::Check(format!("{:?}", parseable)))
        }
    }

    pub fn check(self, parseable: impl ToFormula + Clone + Debug) -> Result<Self, ParseError> {
        self.checkr(parseable)?;
        Ok(self)
    }
    pub fn chk(&self, parseable: impl ToFormula + Clone + Debug) {
        self.checkr(parseable).expect("chk");
    }
}
