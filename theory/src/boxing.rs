use std::ops::Deref;

use crate::gen::{peel_foralls, TheoremGen, TheoryError};
use kernel::pa_axiom::Theorem;
use kernel::pa_formula::{Formula, FormulaVars};
use kernel::pa_parse::{ToFormula,ToExpr};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Boxing {
    Var(String),
    Hyp(FormulaVars),
}

pub trait TheoremBox: Sized {
    fn box_a1(a: impl ToFormula, b: impl ToFormula, boxes: &[Boxing]) -> Result<Self, TheoryError>;
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
    fn box_a5(
        a: FormulaVars,
        x: &str,
        boxes: &[Boxing],
    ) -> Result<Self, TheoryError>;
    fn box_mp(self, other: Self, boxes: &[Boxing]) -> Result<Self, TheoryError>;
    /// Take a formula from outside a box (or boxes) into a box.
    ///
    /// In practice this means inserting zero or more "forall x" or "h ->" into the formula
    /// at the specified points.
    ///
    /// `depth` indicates how many boxes it's already in.
    ///
    /// ```
    /// use kernel::pa_axiom::Theorem;
    /// use theory::boxing::{Boxes,TheoremBox};
    ///
    /// let mut boxes = Boxes::default();
    /// boxes.push_var("x").unwrap();
    /// let t1 = Theorem::box_a1("x = x", "x = 0", &boxes).unwrap();
    /// boxes.push_hyp("x = x").unwrap();
    /// boxes.push_var("y").unwrap();
    /// t1.chk("@x(x = x -> x = 0 -> x = x)");
    /// t1.import(2, &boxes).unwrap().chk("@x(x = x -> @y(x = 0 -> x = x))");
    /// ```
    fn import(self, depth: usize, boxes: &[Boxing]) -> Result<Self, TheoryError>;

    /// Take a formula from the global context (no boxes), import it into a box
    /// and substitute some variables.
    ///
    /// In this example, the variable name `x` is peeled off and then reused. This
    /// is ok.
    ///
    /// ```
    /// use kernel::pa_axiom::Theorem;
    /// use theory::boxing::{Boxes,TheoremBox};
    ///
    /// let mut boxes = Boxes::default();
    /// boxes.push_var("x").unwrap();
    /// boxes.push_hyp("x = x").unwrap();
    ///
    /// let aa1 = Theorem::aa1();
    /// aa1.chk("@x(x + 0 = x)");
    ///
    /// let t = aa1.import_subst(&boxes, &["S(x)"]).unwrap();
    /// t.chk("@x(x = x -> S(x) + 0 = S(x))");
    /// ```
    fn import_subst(self, boxes: &[Boxing], exprs: &[impl ToExpr+Clone]) -> Result<Self, TheoryError>;
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
    fn box_a1(a: impl ToFormula, b: impl ToFormula, boxes: &[Boxing]) -> Result<Self, TheoryError> {
        let xs = just_vars(boxes);
        let t = Theorem::a1(a.to_formula()?, b.to_formula()?, &xs)?;
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

    fn box_a5(
        a: FormulaVars,
        x: &str,
        boxes: &[Boxing],
    ) -> Result<Self, TheoryError> {
        let xs = just_vars(boxes);
        let t = Theorem::a5(a, x, &xs)?;
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

    fn import(self, depth: usize, boxes: &[Boxing]) -> Result<Self, TheoryError> {
        if depth == boxes.len() {
            Ok(self)
        } else if depth > boxes.len() {
            Err(TheoryError::ImportDepthTooGreat)
        } else {
            let f = peel_box_exact(self.formula(), &boxes[0..depth])?;
            match &boxes[depth] {
                Boxing::Var(x) => {
                    // self: ...f
                    let t0 = Theorem::box_a5(f, x, &boxes[0..depth])?;   // ...(f -> @x(f))
                    let t1 = t0.box_mp(self, &boxes[0..depth])?;         // ...@x(f)
                    t1.import(depth + 1, boxes)
                }
                Boxing::Hyp(h) => {
                    // self: ...f
                    let t0 = Theorem::box_a1(f.clone(), h.clone(), &boxes[0..depth])?;   // ...(f -> (h -> f))
                    let t1 = t0.box_mp(self, &boxes[0..depth])?;         // ...(h -> f)
                    t1.import(depth + 1, boxes)
                }
            }
        }
    }

    fn import_subst(self, boxes: &[Boxing], exprs: &[impl ToExpr+Clone]) -> Result<Self, TheoryError> {
        let xs = just_vars(boxes);
        let mut es = vec![];
        for expr in exprs {
            es.push(expr.clone().to_expr()?);
        }
        let t = self.subst_gen(&es, &xs)?;
        install_hyps(t, boxes, &xs)
    }
}

#[derive(Clone,Debug,Default,Eq,PartialEq)]
pub struct Boxes(Vec<Boxing>);

impl Deref for Boxes {
    type Target = [Boxing];
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl Boxes {
    /// Pushes a variable onto the stack of boxes (representing "for all" quantification).
    ///
    /// An error will be returned if a variable of the same name is already on the stack.
    ///
    /// ```
    /// use theory::boxing::Boxes;
    ///
    /// let mut boxes = Boxes::default();
    /// boxes.push_var("x").unwrap();
    /// boxes.push_var("x").expect_err("x is already on the stack");
    /// ```
    ///
    /// Note that vars and hyps can be interleaved. It's ok for an outer hypothesis to have
    /// a bound variable of the same name as the one we're pushing. For example:
    ///
    /// ```
    /// use theory::boxing::Boxes;
    ///
    /// let mut boxes = Boxes::default();
    /// boxes.push_hyp("@x(x = 0)").unwrap();
    /// boxes.push_var("x").expect("This x won't conflict with the other x");
    /// ```
    pub fn push_var(&mut self, x: &str) -> Result<(), TheoryError> {
        for b in &self.0 {
            if let Boxing::Var(y) = b {
                if x == y {
                    return Err(TheoryError::BoxVarConflict(y.clone()));
                }
            }
        }
        self.0.push(Boxing::Var(x.to_owned()));
        Ok(())
    }

    /// Return a vector of the bound variables, in order starting from the outermost.
    ///
    /// ```
    /// use theory::boxing::Boxes;
    ///
    /// let mut boxes = Boxes::default();
    /// boxes.push_var("x").unwrap();
    /// boxes.push_hyp("x = x").unwrap();   // bound() will skip over this because it's not a var
    /// boxes.push_var("y").unwrap();
    /// assert_eq!(boxes.bound(), vec!["x".to_owned(), "y".to_owned()]);
    /// ```
    pub fn bound(&self) -> Vec<String> {
        let mut result = vec![];
        for b in &self.0 {
            if let Boxing::Var(x) = b {
                result.push(x.clone());
            }
        }
        result
    }

    /// Pushes a hypothesis onto the stack of boxes.
    ///
    /// An error will be returned if the formula contains free variables that are not bound by
    /// one of the outer boxes. There will also be an error if it contains bound variables that
    /// are bound by an outer box.
    ///
    /// ```
    /// use theory::boxing::Boxes;
    ///
    /// let mut boxes = Boxes::default();
    /// boxes.push_var("x").unwrap();
    /// boxes.push_hyp("x = y").expect_err("fails because y is not bound. x is though");
    /// ```
    ///
    /// ```
    /// use theory::boxing::Boxes;
    ///
    /// let mut boxes = Boxes::default();
    /// boxes.push_var("x").unwrap();
    /// boxes.push_hyp("@x(x = x)").expect_err("fails because x is bound twice");
    /// ```
    pub fn push_hyp(&mut self, hyp: impl ToFormula) -> Result<(), TheoryError> {
        let f = hyp.to_formula()?;
        let bounds = self.bound();
        for x in f.bound() {
            if bounds.contains(x) {
                return Err(TheoryError::BoxHypBound(x.clone()));
            }
        }
        for x in f.free() {
            if !bounds.contains(x) {
                return Err(TheoryError::BoxHypFree(x.clone()));
            }
        }
        self.0.push(Boxing::Hyp(f));
        Ok(())
    }

    /// Pops something off the top of the stack of boxes (either a variable or a hypothesis)
    ///
    /// ```
    /// use theory::boxing::Boxes;
    ///
    /// let mut boxes = Boxes::default();
    /// boxes.push_var("x").unwrap();
    /// boxes.push_hyp("x = 0").unwrap();
    /// boxes.pop().unwrap();
    /// boxes.pop().unwrap();
    /// boxes.pop().expect_err("Stack should be empty");
    /// ```
    pub fn pop(&mut self) -> Result<(), TheoryError> {
        if self.0.is_empty() {
            Err(TheoryError::BoxEmptyStack)
        } else {
            self.0.pop();
            Ok(())
        }
    }
}

#[cfg(test)]
mod test {
    use super::{Boxing, TheoremBox};
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
