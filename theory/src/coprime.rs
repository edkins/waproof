use crate::boxing::TheoremBox;
use crate::eq::TheoremEq;
use crate::util::{prove, Memo};
use kernel::pa_axiom::Theorem;
use kernel::pa_convenience::num;
use kernel::pa_formula::{Expr, Formula, SyntaxError};

pub fn coprime(a: Expr, b: Expr) -> Result<Formula, SyntaxError> {
    let xx = "coprime:x";
    let yy = "coprime:x";
    let zz = "coprime:x";
    let x = Expr::var(xx);
    let y = Expr::var(yy);
    let z = Expr::var(zz);
    x.clone()
        .mul(y)
        .eq(a)
        .and(x.clone().mul(z).eq(b))?
        .imp(x.eq(num(1)))?
        .forall(zz)?
        .forall(yy)?
        .forall(xx)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_coprime() {
        coprime_0_1().chk(coprime(num(0), num(1)).unwrap());
    }
}

pub fn coprime_0_1() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove(&RESULT, |mut boxes| {
        let x = boxes.push_var_and_get("coprime:x")?;
        let y = boxes.push_var_and_get("coprime:y")?;
        let z = boxes.push_var_and_get("coprime:z")?;
        let hyp = boxes.push_and_get(x.clone().mul(y).eq(num(0)))?;
        panic!();
    })
}
