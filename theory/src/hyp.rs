use crate::gen::{self, TheoremGen, TheoryError};
use kernel::pa_axiom::Theorem;
use kernel::pa_formula::{Formula, FormulaVars};

pub trait TheoremHyp: Sized {
    fn add_hyp(self, h: FormulaVars, depth: usize) -> Result<Self, TheoryError>;
    fn compose(self, other: Self, depth: usize) -> Result<Self, TheoryError>;
}

pub fn get_hyp(f: &Formula, depth: usize) -> Result<FormulaVars, TheoryError> {
    if depth == 0 {
        match f {
            Formula::Imp(h, _) => Ok(h.reconstitute()?),
            _ => Err(TheoryError::NotImp),
        }
    } else {
        match f {
            Formula::ForAll(_, g) => get_hyp(&g, depth - 1),
            _ => Err(TheoryError::NotForAll),
        }
    }
}

pub fn get_conc(f: &Formula, depth: usize) -> Result<FormulaVars, TheoryError> {
    if depth == 0 {
        match f {
            Formula::Imp(_, c) => Ok(c.reconstitute()?),
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
    fn add_hyp(self, h: FormulaVars, depth: usize) -> Result<Self, TheoryError> {
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

        let a = get_hyp(ab.formula(), 0)?;
        let b0 = get_conc(ab.formula(), 0)?;
        let b1 = get_hyp(bc.formula(), 0)?;
        let c = get_conc(bc.formula(), 0)?;
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
