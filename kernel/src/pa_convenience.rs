use crate::pa_formula::{Expr, ExprVars, Formula, FormulaVars, SyntaxError};

////////////////
//
// Reconstitute: obtain the free/bound vars from a given formula, using the cached ("memo") version
// if available
//
////////////////

impl Expr {
    pub fn reconstitute(&self) -> ExprVars {
        match self {
            Expr::Var(x) => ExprVars::var(x),
            Expr::Z => ExprVars::z(),
            Expr::S(e) => e.reconstitute().s(),
            Expr::Add(a, b) => a.reconstitute().add(b.reconstitute()),
            Expr::Mul(a, b) => a.reconstitute().mul(b.reconstitute()),
        }
    }
}

impl Formula {
    pub fn reconstitute(&self) -> Result<FormulaVars, SyntaxError> {
        Ok(match self {
            Formula::False => FormulaVars::falsehood(),
            Formula::Eq(a, b) => a.reconstitute().eq(b.reconstitute()),
            Formula::Imp(p, q) => p.reconstitute()?.imp(q.reconstitute()?)?,
            Formula::ForAll(x, p) => p.reconstitute()?.forall(&x)?,
            Formula::Memo(m) => m.clone().memo(),
        })
    }
}

////////////////
//
// Other logical primitives
//
////////////////

impl FormulaVars {
    pub fn not(self) -> FormulaVars {
        self.imp(FormulaVars::falsehood()).unwrap() // won't fail because falsehood has empty var lists
    }

    pub fn or(self, other: Self) -> Result<FormulaVars, SyntaxError> {
        self.not().imp(other)
    }

    // Truth table:
    // x    y      x->y     x->!y    !(x->!y)
    // 0    0      1        1        0
    // 0    1      1        1        0
    // 1    0      0        1        0
    // 1    1      1        0        1
    pub fn and(self, other: Self) -> Result<FormulaVars, SyntaxError> {
        Ok(self.imp(other.not())?.not())
    }

    pub fn exists(self, x: &str) -> Result<FormulaVars, SyntaxError> {
        Ok(self.not().forall(x)?.not())
    }
}

////////////////
//
// Numbers
//
////////////////

pub fn num(n: usize) -> ExprVars {
    match n {
        0 => ExprVars::z(),
        1 => ExprVars::z().s(),
        2 => ExprVars::z().s().s(),
        _ => {
            if (n & 1) == 1 {
                num(n >> 1).mul(num(2)).s()
            } else {
                num(n >> 1).mul(num(2))
            }
        }
    }
}
