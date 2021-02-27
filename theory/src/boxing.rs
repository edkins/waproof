use crate::gen::{peel_foralls, TheoremGen, TheoryError};
use kernel::pa_axiom::Theorem;
use kernel::pa_formula::{Formula, FormulaVars};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Boxing {
    Var(String),
    Hyp(FormulaVars),
}

pub trait TheoremBox: Sized {
    fn box_a1(a: FormulaVars, b: FormulaVars, boxes: &[Boxing]) -> Result<Self, TheoryError>;
    fn box_a2(
        a: FormulaVars,
        b: FormulaVars,
        c: FormulaVars,
        boxes: &[Boxing],
    ) -> Result<Self, TheoryError>;
    fn box_a4(
        a: FormulaVars,
        b: FormulaVars,
        x: &str,
        boxes: &[Boxing],
    ) -> Result<Self, TheoryError>;
    fn box_mp(self, other: Self, boxes: &[Boxing]) -> Result<Self, TheoryError>;
}

pub fn peel_box_exact(a: &FormulaVars, boxes: &[Boxing]) -> Result<FormulaVars, TheoryError> {
    let mut f = a.formula();
    for b in boxes {
        match &f {
            Formula::ForAll(x, f2) => {
                if *b != Boxing::Var(x.clone()) {
                    return Err(TheoryError::BoxMismatch);
                }
                f = f2;
            }
            Formula::Imp(f1, f2) => {
                if *b != Boxing::Hyp(f1.reconstitute()?) {
                    return Err(TheoryError::BoxMismatch);
                }
                f = f2;
            }
            _ => return Err(TheoryError::NotForAllOrHyp),
        }
    }
    Ok(f.reconstitute()?)
}

pub fn peel_box(a: &FormulaVars, depth: usize) -> Result<(Vec<Boxing>, FormulaVars), TheoryError> {
    let mut boxes = vec![];
    let mut f = a.formula();
    for _ in 0..depth {
        match f {
            Formula::ForAll(x, f2) => {
                boxes.push(Boxing::Var(x.clone()));
                f = f2;
            }
            Formula::Imp(f1, f2) => {
                boxes.push(Boxing::Hyp(f1.reconstitute()?));
                f = f2;
            }
            _ => return Err(TheoryError::NotForAllOrHyp),
        }
    }
    Ok((boxes, f.reconstitute()?))
}

fn just_vars(boxes: &[Boxing]) -> Vec<String> {
    let mut result = vec![];
    for b in boxes {
        if let Boxing::Var(x) = b {
            result.push(x.clone());
        }
    }
    result
}

fn install_hyps(
    mut t: Theorem,
    boxes: &[Boxing],
    mut xs: &[String],
) -> Result<Theorem, TheoryError> {
    for b in boxes.iter().rev() {
        match b {
            Boxing::Var(_) => xs = &xs[0..xs.len() - 1],
            Boxing::Hyp(h) => {
                let (_, f) = peel_foralls(t.formula(), xs.len())?;
                // t: @xs...f
                let t2 = Theorem::a1(f, h.clone(), xs)?; // @xs...(f -> (h -> f))
                t = t2.gen_mp(t, xs.len())?; // @xs...(h -> f)
            }
        }
    }
    Ok(t)
}

impl TheoremBox for Theorem {
    fn box_a1(a: FormulaVars, b: FormulaVars, boxes: &[Boxing]) -> Result<Self, TheoryError> {
        let xs = just_vars(boxes);
        let t = Theorem::a1(a, b, &xs)?;
        install_hyps(t, boxes, &xs)
    }

    fn box_a2(
        a: FormulaVars,
        b: FormulaVars,
        c: FormulaVars,
        boxes: &[Boxing],
    ) -> Result<Self, TheoryError> {
        let xs = just_vars(boxes);
        let t = Theorem::a2(a, b, c, &xs)?;
        install_hyps(t, boxes, &xs)
    }

    fn box_a4(
        a: FormulaVars,
        b: FormulaVars,
        x: &str,
        boxes: &[Boxing],
    ) -> Result<Self, TheoryError> {
        let xs = just_vars(boxes);
        let t = Theorem::a4(a, b, x, &xs)?;
        install_hyps(t, boxes, &xs)
    }

    fn box_mp(self, other: Self, boxes: &[Boxing]) -> Result<Self, TheoryError> {
        if boxes.is_empty() {
            Ok(self.mp(other)?)
        } else {
            let ab = peel_box_exact(self.formula(), boxes)?;
            let a = peel_box_exact(other.formula(), boxes)?;
            let b = match ab.formula() {
                Formula::Imp(h, af) => {
                    if **h != *a.formula() {
                        return Err(TheoryError::WrongHyp);
                    }
                    af.reconstitute()?
                }
                _ => return Err(TheoryError::NotImp),
            };

            match &boxes[boxes.len() - 1] {
                Boxing::Var(x) => {
                    // self: ...@x(a->b)
                    // other: ...@x(a)
                    let t0 = Theorem::box_a4(a, b, &x, &boxes[0..boxes.len() - 1])?; // ...(@x(a->b)->(@x(a)->@x(b)))
                    let t1 = t0.box_mp(self, &boxes[0..boxes.len() - 1])?;
                    let t2 = t1.box_mp(other, &boxes[0..boxes.len() - 1])?;
                    Ok(t2)
                }
                Boxing::Hyp(h) => {
                    // self: ...(h->a->b)
                    // other: ...(h->a)
                    let t0 = Theorem::box_a2(h.clone(), a, b, &boxes[0..boxes.len() - 1])?; // ...((h->a->b)->(h->a)->(h->b))
                    let t1 = t0.box_mp(self, &boxes[0..boxes.len() - 1])?;
                    let t2 = t1.box_mp(other, &boxes[0..boxes.len() - 1])?;
                    Ok(t2)
                }
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::{Boxing, TheoremBox};
    use crate::gen::TheoremGen;
    use kernel::pa_axiom::Theorem;
    use kernel::pa_convenience::num;
    use kernel::pa_formula::ExprVars;

    fn x() -> ExprVars {
        ExprVars::var("x")
    }
    fn y() -> ExprVars {
        ExprVars::var("y")
    }

    #[test]
    fn x_imp_y_imp_a2() {
        Theorem::box_a2(
            x().eq(x()),
            y().eq(y()),
            x().eq(y()),
            &[
                Boxing::Var("x".to_owned()),
                Boxing::Hyp(x().eq(num(0))),
                Boxing::Var("y".to_owned()),
                Boxing::Hyp(y().eq(num(0))),
            ],
        )
        .unwrap()
        .check("@x(x=0 -> @y(y=0 -> ((x=x -> y=y -> x=y) -> (x=x -> y=y) -> (x=x -> x=y))))")
        .unwrap();
    }

    #[test]
    fn x_y_a2() {
        Theorem::box_a2(
            x().eq(x()),
            y().eq(y()),
            x().eq(y()),
            &[Boxing::Var("x".to_owned()), Boxing::Var("y".to_owned())],
        )
        .unwrap()
        .check("@x(@y(((x=x -> y=y -> x=y) -> (x=x -> y=y) -> (x=x -> x=y))))")
        .unwrap();
    }
    #[test]
    fn x_imp_y_imp_mp() {
        let bs = &[
            Boxing::Var("x".to_owned()),
            Boxing::Hyp(x().eq(num(0))),
            Boxing::Var("y".to_owned()),
            Boxing::Hyp(y().eq(num(0))),
        ];
        let t1 = Theorem::box_a2(x().eq(x()), y().eq(y()), x().eq(x()), bs)
            .unwrap()
            .check("@x(x=0 -> @y(y=0 -> ((x=x -> y=y -> x=x) -> (x=x -> y=y) -> (x=x -> x=x))))")
            .unwrap();

        let t2 = Theorem::box_a1(x().eq(x()), y().eq(y()), bs)
            .unwrap()
            .check("@x(x=0 -> @y(y=0 -> (x=x -> y=y -> x=x)))")
            .unwrap();

        t1.box_mp(t2, bs)
            .unwrap()
            .check("@x(x=0 -> @y(y=0 -> (x=x -> y=y) -> (x=x -> x=x)))")
            .unwrap();
    }
}
