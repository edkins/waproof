use crate::pa_axiom::Theorem;
use crate::pa_convenience::num;
use crate::pa_formula::{ExprVars, FormulaVars, SyntaxError};
use nom::branch::alt;
use nom::bytes::complete::{tag, take_while};
use nom::character::complete::{digit1, multispace0, satisfy};
use nom::combinator::{all_consuming, opt, recognize, value};
use nom::error::ErrorKind;
use nom::sequence::{delimited, pair, preceded, terminated};
use nom::IResult;
use std::fmt::Debug;
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

fn syn(e: SyntaxError) -> nom::Err<ParseError> {
    nom::Err::Error(ParseError::Syntax(e))
}

fn extract_parse_error(e: nom::Err<ParseError>) -> ParseError {
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

fn parse_sym(sym: &'static str) -> impl Fn(&str) -> IResult<&str, (), ParseError> {
    move |input| {
        let (input, _) = multispace0(input)?;
        let (input, _) = tag(sym)(input)?;
        Ok((input, ()))
    }
}

fn parse_keyword(sym: &'static str) -> impl Fn(&str) -> IResult<&str, (), ParseError> {
    move |input| {
        let (input, _) = multispace0(input)?;
        let (input, _) = tag(sym)(input)?;
        let (input, _) = not_at_alphanum(input)?;
        Ok((input, ()))
    }
}

fn parse_var_str(input: &str) -> IResult<&str, &str, ParseError> {
    let (input, _) = multispace0(input)?;
    let (input, word) = recognize(pair(satisfy(starts_word), take_while(continues_word)))(input)?;
    Ok((input, word))
}

fn parse_var(input: &str) -> IResult<&str, ExprVars, ParseError> {
    let (input, x) = parse_var_str(input)?;
    Ok((input, ExprVars::var(x)))
}

fn parse_number(input: &str) -> IResult<&str, ExprVars, ParseError> {
    let (input, _) = multispace0(input)?;
    let (input, number) = digit1(input)?;
    let (input, _) = not_at_alphanum(input)?;
    let n = number
        .parse()
        .map_err(|_| nom::Err::Error(ParseError::NumberTooBig))?;
    Ok((input, num(n)))
}

fn parse_s(input: &str) -> IResult<&str, ExprVars, ParseError> {
    let (input, _) = parse_keyword("S")(input)?;
    let (input, _) = parse_sym("(")(input)?;
    let (input, e) = parse_expr(input)?;
    let (input, _) = parse_sym(")")(input)?;
    Ok((input, e.s()))
}

fn parse_paren(input: &str) -> IResult<&str, ExprVars, ParseError> {
    delimited(parse_sym("("), parse_expr, parse_sym(")"))(input)
}

fn parse_term(input: &str) -> IResult<&str, ExprVars, ParseError> {
    alt((parse_paren, parse_s, parse_number, parse_var))(input)
}

fn parse_muls(input: &str) -> IResult<&str, ExprVars, ParseError> {
    let (input, a) = parse_term(input)?;
    let (input, mb) = opt(preceded(parse_sym("*"), parse_muls))(input)?;
    let r = match mb {
        None => a,
        Some(b) => a.mul(b),
    };
    Ok((input, r))
}

fn parse_expr(input: &str) -> IResult<&str, ExprVars, ParseError> {
    let (input, a) = parse_muls(input)?;
    let (input, mb) = opt(preceded(parse_sym("+"), parse_expr))(input)?;
    let r = match mb {
        None => a,
        Some(b) => a.add(b),
    };
    Ok((input, r))
}

impl FromStr for ExprVars {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(terminated(all_consuming(parse_expr), multispace0)(s)
            .map_err(extract_parse_error)?
            .1)
    }
}

fn parse_false(input: &str) -> IResult<&str, FormulaVars, ParseError> {
    value(FormulaVars::falsehood(), parse_keyword("false"))(input)
}

fn parse_eq(input: &str) -> IResult<&str, FormulaVars, ParseError> {
    let (input, a) = parse_expr(input)?;
    let (input, _) = parse_sym("=")(input)?;
    let (input, b) = parse_expr(input)?;
    Ok((input, a.eq(b)))
}

fn parse_paren_formula(input: &str) -> IResult<&str, FormulaVars, ParseError> {
    delimited(parse_sym("("), parse_formula, parse_sym(")"))(input)
}

fn parse_not(input: &str) -> IResult<&str, FormulaVars, ParseError> {
    let (input, f) = preceded(parse_sym("!"), parse_tight)(input)?;
    Ok((input, f.not()))
}

fn parse_forall(input: &str) -> IResult<&str, FormulaVars, ParseError> {
    let (input, _) = parse_sym("@")(input)?;
    let (input, x) = parse_var_str(input)?;
    let (input, f) = delimited(parse_sym("("), parse_formula, parse_sym(")"))(input)?;
    Ok((input, f.forall(x).map_err(syn)?))
}

fn parse_exists(input: &str) -> IResult<&str, FormulaVars, ParseError> {
    let (input, _) = parse_sym("#")(input)?;
    let (input, x) = parse_var_str(input)?;
    let (input, f) = delimited(parse_sym("("), parse_formula, parse_sym(")"))(input)?;
    Ok((input, f.exists(x).map_err(syn)?))
}

fn parse_tight(input: &str) -> IResult<&str, FormulaVars, ParseError> {
    alt((
        parse_paren_formula,
        parse_false,
        parse_forall,
        parse_exists,
        parse_not,
        parse_eq,
    ))(input)
}

fn parse_imps(input: &str) -> IResult<&str, FormulaVars, ParseError> {
    let (input, a) = parse_tight(input)?;
    let (input, mb) = opt(preceded(parse_sym("->"), parse_imps))(input)?;
    let r = match mb {
        None => a,
        Some(b) => a.imp(b).map_err(syn)?,
    };
    Ok((input, r))
}

fn parse_ands(input: &str) -> IResult<&str, FormulaVars, ParseError> {
    let (input, a) = parse_imps(input)?;
    let (input, mb) = opt(preceded(parse_sym("&"), parse_ands))(input)?;
    let r = match mb {
        None => a,
        Some(b) => a.and(b).map_err(syn)?,
    };
    Ok((input, r))
}

fn parse_formula(input: &str) -> IResult<&str, FormulaVars, ParseError> {
    let (input, a) = parse_ands(input)?;
    let (input, mb) = opt(preceded(parse_sym("|"), parse_formula))(input)?;
    let r = match mb {
        None => a,
        Some(b) => a.or(b).map_err(syn)?,
    };
    Ok((input, r))
}

impl FromStr for FormulaVars {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(terminated(all_consuming(parse_formula), multispace0)(s)
            .map_err(extract_parse_error)?
            .1)
    }
}

pub trait ToFormula {
    fn to_formula(self) -> Result<FormulaVars, ParseError>;
}

impl ToFormula for FormulaVars {
    fn to_formula(self) -> Result<FormulaVars, ParseError> {
        Ok(self)
    }
}

impl ToFormula for &FormulaVars {
    fn to_formula(self) -> Result<FormulaVars, ParseError> {
        Ok(self.clone())
    }
}

impl ToFormula for &str {
    fn to_formula(self) -> Result<FormulaVars, ParseError> {
        self.parse()
    }
}

pub trait ToExpr {
    fn to_expr(self) -> Result<ExprVars, ParseError>;
}

impl ToExpr for ExprVars {
    fn to_expr(self) -> Result<ExprVars, ParseError> {
        Ok(self)
    }
}

impl ToExpr for &ExprVars {
    fn to_expr(self) -> Result<ExprVars, ParseError> {
        Ok(self.clone())
    }
}

impl ToExpr for &str {
    fn to_expr(self) -> Result<ExprVars, ParseError> {
        self.parse()
    }
}

impl Theorem {
    pub fn checkr(&self, parseable: impl ToFormula + Clone + Debug) -> Result<(), ParseError> {
        if parseable.clone().to_formula()? == *self.formula() {
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
