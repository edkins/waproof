use crate::boxing::Boxes;
use crate::process;
use kernel::pa_axiom::{Theorem, TheoremError};
use kernel::pa_formula::SyntaxError;
use kernel::pa_parse::ParseError;
use std::cell::RefCell;

#[derive(Debug)]
pub enum TheoryError {
    Syntax(SyntaxError),
    Axiom(TheoremError),
    Parse(ParseError),
    BoxEmptyStack,
    BoxVarConflict(String),
    BoxHypBound(String),
    BoxHypFree(String),
    BoxMismatch,
    CheckMismatch(String),
    ComposeMismatch,
    ImportDepthTooGreat,
    NoSuitableTheoremFound,
    NoTheorem,
    NotAbsentGen(String),
    NotEquality,
    NotFalse,
    NotForAll,
    NotForAllOrHyp,
    NotImp,
    NotOuterVar(String),
    NotReorder(String),
    PushingPastFreeVar(String),
    RenameInnerConflict(String),
    RenameOuterConflict(String),
    StructuralMismatch,
    SubstNotInEnvironment(String),
    SubstInnerConflict(String),
    SubstOuterConflict(String),
    UnclosedBox,
    VarMismatch(String, String),
    WrongHyp,
}

impl From<SyntaxError> for TheoryError {
    fn from(e: SyntaxError) -> Self {
        TheoryError::Syntax(e)
    }
}

impl From<TheoremError> for TheoryError {
    fn from(e: TheoremError) -> Self {
        TheoryError::Axiom(e)
    }
}

impl From<ParseError> for TheoryError {
    fn from(e: ParseError) -> Self {
        TheoryError::Parse(e)
    }
}

#[derive(Default)]
pub struct Memo(RefCell<Option<Theorem>>);

pub fn prove(
    result: &'static std::thread::LocalKey<Memo>,
    func: impl FnOnce(Boxes) -> Result<Theorem, TheoryError>,
) -> Theorem {
    result.with(|r| {
        r.0.borrow_mut()
            .get_or_insert_with(|| func(Boxes::default()).expect("proof failure"))
            .clone()
    })
}

pub fn prove_with_script(
    result: &'static std::thread::LocalKey<Memo>,
    script: &str,
    references: &[Theorem],
) -> Theorem {
    result.with(|r| {
        r.0.borrow_mut()
            .get_or_insert_with(|| {
                process::prove_script(script, references).expect("proof failure")
            })
            .clone()
    })
}
