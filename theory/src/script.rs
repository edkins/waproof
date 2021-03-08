use kernel::pa_formula::{Expr, Formula};
use kernel::pa_parse::{
    extract_parse_error, parse_expr, parse_formula, parse_keyword, parse_sym, parse_var_str,
    ParseError,
};
use nom::branch::alt;
use nom::character::complete::multispace0;
use nom::combinator::{all_consuming, map, value};
use nom::multi::{many1, separated_list1};
use nom::sequence::terminated;
use nom::IResult;
use std::str::FromStr;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ScriptEl {
    PushVar(String),
    PushHyp(Formula),
    Pop,
    Chain(Vec<Expr>),
    Import(Formula),
    Induction,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Script(pub Vec<ScriptEl>);

fn parse_push_var(input: &str) -> IResult<&str, ScriptEl, ParseError> {
    let (input, _) = parse_keyword("var")(input)?;
    let (input, x) = parse_var_str(input)?;
    let (input, _) = parse_sym("{")(input)?;
    Ok((input, ScriptEl::PushVar(x.to_owned())))
}

fn parse_push_hyp(input: &str) -> IResult<&str, ScriptEl, ParseError> {
    let (input, _) = parse_keyword("hyp")(input)?;
    let (input, f) = parse_formula(input)?;
    let (input, _) = parse_sym("{")(input)?;
    Ok((input, ScriptEl::PushHyp(f)))
}

fn parse_pop(input: &str) -> IResult<&str, ScriptEl, ParseError> {
    value(ScriptEl::Pop, parse_sym("}"))(input)
}

fn parse_chain(input: &str) -> IResult<&str, ScriptEl, ParseError> {
    let (input, _) = parse_keyword("chain")(input)?;
    let (input, exprs) = separated_list1(parse_sym("="), parse_expr)(input)?;
    let (input, _) = parse_sym(";")(input)?;
    Ok((input, ScriptEl::Chain(exprs)))
}

fn parse_import(input: &str) -> IResult<&str, ScriptEl, ParseError> {
    let (input, _) = parse_keyword("import")(input)?;
    let (input, f) = parse_formula(input)?;
    let (input, _) = parse_sym(";")(input)?;
    Ok((input, ScriptEl::Import(f)))
}

fn parse_induction(input: &str) -> IResult<&str, ScriptEl, ParseError> {
    value(
        ScriptEl::Induction,
        terminated(parse_keyword("induction"), parse_sym(";")),
    )(input)
}

fn parse_el(input: &str) -> IResult<&str, ScriptEl, ParseError> {
    alt((
        parse_push_var,
        parse_push_hyp,
        parse_pop,
        parse_chain,
        parse_import,
        parse_induction,
    ))(input)
}

fn parse_script(input: &str) -> IResult<&str, Script, ParseError> {
    map(many1(parse_el), Script)(input)
}

impl FromStr for Script {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let result = all_consuming(terminated(parse_script, multispace0))(s)
            .map_err(extract_parse_error)?
            .1;
        Ok(result)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn parse_induction() {
        assert_eq!(parse_el("induction;").unwrap(), ("", ScriptEl::Induction))
    }

    #[test]
    fn parse_just_induction() {
        assert_eq!(
            "induction;".parse::<Script>().unwrap(),
            Script(vec![ScriptEl::Induction])
        )
    }

    #[test]
    fn parse_just_induction_nl() {
        assert_eq!(
            "
induction;
"
            .parse::<Script>()
            .unwrap(),
            Script(vec![ScriptEl::Induction])
        )
    }
}
