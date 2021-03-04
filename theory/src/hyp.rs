use crate::gen::{self, TheoremGen};
use crate::util::TheoryError;
use kernel::pa_axiom::Theorem;
use kernel::pa_formula::{Formula};

pub trait TheoremHyp: Sized {
    fn add_hyp(self, h: Formula, depth: usize) -> Result<Self, TheoryError>;
    fn compose(self, other: Self, depth: usize) -> Result<Self, TheoryError>;
}

pub fn get_hyp(f: &Formula, depth: usize) -> Result<Formula, TheoryError> {
    if depth == 0 {
        match f {
            Formula::Imp(h, _) => Ok((**h).clone()),
            _ => Err(TheoryError::NotImp),
        }
    } else {
        match f {
            Formula::ForAll(_, g) => get_hyp(&g, depth - 1),
            _ => Err(TheoryError::NotForAll),
        }
    }
}

pub fn get_conc(f: &Formula, depth: usize) -> Result<Formula, TheoryError> {
    if depth == 0 {
        match f {
            Formula::Imp(_, c) => Ok((**c).clone()),
            _ => Err(TheoryError::NotImp),
        }
    } else {
        match f {
            Formula::ForAll(_, g) => get_conc(&g, depth - 1),
            _ => Err(TheoryError::NotForAll),
        }
    }
}

impl TheoremHyp for Theorem {
    fn add_hyp(self, h: Formula, depth: usize) -> Result<Self, TheoryError> {
        let (vars, a) = gen::peel_foralls(self.formula(), depth)?;
        // self: @v...A
        let aba = Theorem::a1(a, h, &vars)?; // @v...(A->(B->A))
        aba.gen_mp(self, depth)
    }

    fn compose(self, other: Self, depth: usize) -> Result<Self, TheoryError> {
        let (vars, ab) = gen::peel_foralls(self.formula(), depth)?;
        let (others, bc) = gen::peel_foralls(other.formula(), depth)?;
        for i in 0..depth - 1 {
            if vars[i] != others[i] {
                return Err(TheoryError::VarMismatch(vars[i].clone(), others[i].clone()));
            }
        }

        let a = get_hyp(&ab, 0)?;
        let b0 = get_conc(&ab, 0)?;
        let b1 = get_hyp(&bc, 0)?;
        let c = get_conc(&bc, 0)?;
        if b0 != b1 {
            return Err(TheoryError::ComposeMismatch);
        }

        // self:  @v...(A -> B)
        // other: @v...(B -> C)
        let t0 = other.add_hyp(a.clone(), depth)?; // @v...(A -> B -> C)
        let t1 = Theorem::a2(a, b0, c, &vars)?; // @v...((A -> B -> C) -> (A -> B) -> (A -> C))
        t1.gen_mp(t0, depth)?.gen_mp(self, depth) // @v...(A->C)
    }
}
