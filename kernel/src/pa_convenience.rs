use crate::pa_formula::{Expr, Formula, SyntaxError};
use std::ops::Not;

////////////////
//
// Other logical primitives
//
////////////////

impl Not for Formula {
    type Output = Self;

    fn not(self) -> Self::Output {
        self.imp(Formula::falsehood()).unwrap()
    }
}

impl Formula {
    pub fn or(self, other: Self) -> Result<Formula, SyntaxError> {
        self.not().imp(other)
    }

    // Truth table:
    // x    y      x->y     x->!y    !(x->!y)
    // 0    0      1        1        0
    // 0    1      1        1        0
    // 1    0      0        1        0
    // 1    1      1        0        1
    pub fn and(self, other: Self) -> Result<Formula, SyntaxError> {
        Ok(self.imp(other.not())?.not())
    }

    pub fn exists(self, x: &str) -> Result<Formula, SyntaxError> {
        Ok(self.not().forall(x)?.not())
    }
}

////////////////
//
// Numbers
//
////////////////

pub fn num(n: usize) -> Expr {
    match n {
        0 => Expr::z(),
        1 => Expr::z().s(),
        2 => Expr::z().s().s(),
        _ => {
            if (n & 1) == 1 {
                (num(n >> 1) * num(2)).s()
            } else {
                num(n >> 1) * num(2)
            }
        }
    }
}
