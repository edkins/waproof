use std::fmt::Debug;
use std::ops::Deref;

use crate::gen::{self, peel_foralls, TheoremGen};
use crate::util::TheoryError;
use kernel::pa_axiom::Theorem;
use kernel::pa_formula::{Expr, Formula};
use kernel::pa_parse::{ToExpr, ToFormula};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Boxing {
    Var(String),
    Hyp(Formula),
}

impl Boxing {
    pub fn is_var(&self) -> bool {
        match self {
            Boxing::Var(_) => true,
            Boxing::Hyp(_) => false,
        }
    }
}

pub trait TheoremBox: Sized {
    fn box_a1(a: impl ToFormula, b: impl ToFormula, boxes: &[Boxing]) -> Result<Self, TheoryError>;
    fn box_a2(
        a: impl ToFormula,
        b: impl ToFormula,
        c: impl ToFormula,
        boxes: &[Boxing],
    ) -> Result<Self, TheoryError>;
    fn box_a3(a: impl ToFormula, boxes: &[Boxing]) -> Result<Self, TheoryError>;
    fn box_a4(
        a: impl ToFormula,
        b: impl ToFormula,
        x: &str,
        boxes: &[Boxing],
    ) -> Result<Self, TheoryError>;
    fn box_a5(a: impl ToFormula, x: &str, boxes: &[Boxing]) -> Result<Self, TheoryError>;
    fn box_a6(
        a: impl ToFormula,
        x: &str,
        e: impl ToExpr,
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
    fn import_subst(
        self,
        boxes: &[Boxing],
        exprs: &[impl ToExpr + Clone],
    ) -> Result<Self, TheoryError>;

    /// Prove that a formula implies itself, within some boxes.
    ///
    /// ```
    /// use kernel::pa_axiom::Theorem;
    /// use theory::boxing::{Boxes,TheoremBox};
    ///
    /// let mut boxes = Boxes::default();
    /// boxes.push_var("x").unwrap();
    /// boxes.push_var("y").unwrap();
    ///
    /// let t = Theorem::imp_self("x = y", &boxes).unwrap();
    /// t.chk("@x(@y(x = y -> x = y))");
    ///
    /// boxes.push_hyp("x = 0").unwrap();
    /// let t2 = Theorem::imp_self("y = 0", &boxes).unwrap();
    /// t2.chk("@x(@y(x = 0 -> y = 0 -> y = 0))");
    /// ```
    fn imp_self(f: impl ToFormula, boxes: &[Boxing]) -> Result<Self, TheoryError>;

    fn cleave(self, boxes: &[Boxing], extra_depth: usize) -> Result<Self, TheoryError>;
    fn box_subst_one(self, boxes: &[Boxing], e: impl ToExpr) -> Result<Self, TheoryError>;
    fn hyp_syllogism(self, other: Self, boxes: &[Boxing]) -> Result<Self, TheoryError>;

    fn box_chk(&self, parseable: impl ToFormula + Clone + Debug, boxes: &[Boxing]);

    /// Prove a theorem by induction.
    ///
    /// self is ...@x(H[x] -> H[S(x)]
    /// base is ...H[0]
    fn induction(self, base: Self, boxes: &[Boxing]) -> Result<Self, TheoryError>;

    fn push_forall(self, boxes: &[Boxing], extra_depth: usize) -> Result<Self, TheoryError>;
    fn contradiction(self, target: impl ToFormula, boxes: &[Boxing]) -> Result<Self, TheoryError>;
}

pub fn peel_box_exact(a: &Formula, boxes: &[Boxing]) -> Result<Formula, TheoryError> {
    let mut f = a.clone();
    for b in boxes {
        f = f
            .cases(
                || Err(TheoryError::NotForAllOrHyp),
                |_, _| Err(TheoryError::NotForAllOrHyp),
                |f1, f2| {
                    if *b != Boxing::Hyp(f1.clone()) {
                        return Err(TheoryError::BoxMismatch);
                    }
                    Ok(f2)
                },
                |x, f2| {
                    if *b != Boxing::Var(x.to_owned()) {
                        return Err(TheoryError::BoxMismatch);
                    }
                    Ok(f2)
                },
            )?
            .clone();
    }
    Ok(f)
}

pub fn peel_box(a: &Formula, depth: usize) -> Result<(Vec<Boxing>, Formula), TheoryError> {
    let mut boxes = vec![];
    let mut f = a.clone();
    for _ in 0..depth {
        match f_as_enum(&f) {
            FormulaRef::Imp(f1, f2) => {
                boxes.push(Boxing::Hyp(f1.clone()));
                f = f2.clone();
            }
            FormulaRef::ForAll(x, f2) => {
                boxes.push(Boxing::Var(x.to_owned()));
                f = f2.clone();
            }
            _ => return Err(TheoryError::NotForAllOrHyp),
        }
    }
    Ok((boxes, f))
}

pub enum FormulaRef<'a> {
    False,
    Eq(&'a Expr, &'a Expr),
    Imp(&'a Formula, &'a Formula),
    ForAll(&'a str, &'a Formula),
}

pub fn f_as_enum<'a>(f: &'a Formula) -> FormulaRef<'a> {
    f.cases(
        || FormulaRef::False,
        FormulaRef::Eq,
        FormulaRef::Imp,
        FormulaRef::ForAll,
    )
}

pub fn peel_box_until_eq(a: &Formula) -> Result<(Vec<Boxing>, Expr, Expr), TheoryError> {
    let mut boxes = vec![];
    let mut f = a.clone();
    loop {
        match f_as_enum(&f) {
            FormulaRef::False => return Err(TheoryError::NotForAllOrHyp),
            FormulaRef::Eq(left, right) => {
                return Ok((boxes, left.clone(), right.clone()));
            }
            FormulaRef::Imp(f1, f2) => {
                boxes.push(Boxing::Hyp(f1.clone()));
                f = f2.clone();
            }
            FormulaRef::ForAll(x, f2) => {
                boxes.push(Boxing::Var(x.to_owned()));
                f = f2.clone();
            }
        }
    }
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
        a: impl ToFormula,
        b: impl ToFormula,
        c: impl ToFormula,
        boxes: &[Boxing],
    ) -> Result<Self, TheoryError> {
        let xs = just_vars(boxes);
        let t = Theorem::a2(a.to_formula()?, b.to_formula()?, c.to_formula()?, &xs)?;
        install_hyps(t, boxes, &xs)
    }

    fn box_a3(a: impl ToFormula, boxes: &[Boxing]) -> Result<Self, TheoryError> {
        let xs = just_vars(boxes);
        let t = Theorem::a3(a.to_formula()?, &xs)?;
        install_hyps(t, boxes, &xs)
    }

    fn box_a4(
        a: impl ToFormula,
        b: impl ToFormula,
        x: &str,
        boxes: &[Boxing],
    ) -> Result<Self, TheoryError> {
        let xs = just_vars(boxes);
        let t = Theorem::a4(a.to_formula()?, b.to_formula()?, x, &xs)?;
        install_hyps(t, boxes, &xs)
    }

    fn box_a5(a: impl ToFormula, x: &str, boxes: &[Boxing]) -> Result<Self, TheoryError> {
        let xs = just_vars(boxes);
        let t = Theorem::a5(a.to_formula()?, x, &xs)?;
        install_hyps(t, boxes, &xs)
    }

    fn box_a6(
        a: impl ToFormula,
        x: &str,
        e: impl ToExpr,
        boxes: &[Boxing],
    ) -> Result<Self, TheoryError> {
        let xs = just_vars(boxes);
        let t = Theorem::a6(a.to_formula()?, x, e.to_expr()?, &xs)?;
        install_hyps(t, boxes, &xs)
    }

    fn box_mp(self, other: Self, boxes: &[Boxing]) -> Result<Self, TheoryError> {
        if boxes.is_empty() {
            Ok(self.mp(other)?)
        } else {
            let ab = peel_box_exact(self.formula(), boxes)?;
            let a = peel_box_exact(other.formula(), boxes)?;
            let (h, b) = gen::expect_imp(&ab)?;
            if *h != a {
                return Err(TheoryError::WrongHyp);
            }

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

    fn cleave(self, boxes: &[Boxing], extra_depth: usize) -> Result<Self, TheoryError> {
        if extra_depth == 0 {
            Ok(self)
        } else {
            let (all_boxes, ab) = peel_box(self.formula(), boxes.len() + extra_depth)?; // a -> b
            if &all_boxes[0..boxes.len()] != boxes {
                return Err(TheoryError::BoxMismatch);
            }
            let (a, b) = gen::expect_imp(&ab)?;
            let most_boxes = &all_boxes[0..all_boxes.len() - 1];
            match &all_boxes[all_boxes.len() - 1] {
                Boxing::Var(x) => {
                    // self: ... ...@x(a->b)
                    let t0 = Theorem::box_a4(a, b, &x, most_boxes)?; // ...( @x(a->b) -> @x(a) -> @x(b) )
                    let t1 = t0.box_mp(self, most_boxes)?; // ...( @x(a) -> @x(b) )
                    t1.cleave(boxes, extra_depth - 1)
                }
                Boxing::Hyp(h) => {
                    // self: ... ...(h -> a -> b)
                    let t0 = Theorem::box_a2(h, a, b, most_boxes)?; // ...( (h->a->b) -> (h->a) -> (h->b) )
                    let t1 = t0.box_mp(self, most_boxes)?; // ...( (h->a) -> (h->b) )
                    t1.cleave(boxes, extra_depth - 1)
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
                    let t0 = Theorem::box_a5(f, x, &boxes[0..depth])?; // ...(f -> @x(f))
                    let t1 = t0.box_mp(self, &boxes[0..depth])?; // ...@x(f)
                    t1.import(depth + 1, boxes)
                }
                Boxing::Hyp(h) => {
                    // self: ...f
                    let t0 = Theorem::box_a1(f.clone(), h.clone(), &boxes[0..depth])?; // ...(f -> (h -> f))
                    let t1 = t0.box_mp(self, &boxes[0..depth])?; // ...(h -> f)
                    t1.import(depth + 1, boxes)
                }
            }
        }
    }

    fn import_subst(
        self,
        boxes: &[Boxing],
        exprs: &[impl ToExpr + Clone],
    ) -> Result<Self, TheoryError> {
        let xs = just_vars(boxes);
        let mut es = vec![];
        for expr in exprs {
            es.push(expr.clone().to_expr()?);
        }
        let t = self.subst_gen(&es, &xs)?;
        install_hyps(t, boxes, &xs)
    }

    fn imp_self(f: impl ToFormula, boxes: &[Boxing]) -> Result<Self, TheoryError> {
        let a = f.to_formula()?;
        let xs = just_vars(boxes);
        let t1 = Theorem::a1(a.clone(), a.clone().imp(a.clone())?, &xs)?; // @... (x -> (x -> x) -> x)
        let t2 = Theorem::a2(a.clone(), a.clone().imp(a.clone())?, a.clone(), &xs)?; // @... ((x -> (x -> x) -> x) -> (x -> (x -> x)) -> (x -> x) )
        let t3 = t2.gen_mp(t1, xs.len())?; // @... ((x -> (x -> x)) -> (x -> x))
        let t4 = Theorem::a1(a.clone(), a.clone(), &xs)?; // x -> (x -> x)
        let t5 = t3.gen_mp(t4, xs.len())?; // @... (x -> x)
        install_hyps(t5, boxes, &xs)
    }

    fn box_subst_one(self, boxes: &[Boxing], expr: impl ToExpr) -> Result<Self, TheoryError> {
        let xf = peel_box_exact(self.formula(), boxes)?;
        let (x, f) = gen::peel_forall(&xf)?;
        let vars = just_vars(&boxes);

        let e = expr.to_expr()?;
        gen::check_expr_environment(&e, &vars)?;

        if vars.iter().any(|y| *y == *x) {
            return Err(TheoryError::SubstOuterConflict(x.to_owned()));
        }

        // self: ...@x(f[x])
        let t1 = Theorem::box_a6(f, &x, e, &boxes)?; // ...(@x(f[x]) -> f[e])
        t1.box_mp(self, &boxes)
    }

    fn induction(self, base: Self, boxes: &[Boxing]) -> Result<Self, TheoryError> {
        let forall = peel_box_exact(self.formula(), boxes)?;
        let (x, hx_hsx) = gen::expect_forall(&forall)?;
        let (hx, _) = gen::expect_imp(hx_hsx)?;
        if boxes.is_empty() {
            Ok(Theorem::aind(hx.clone(), &x, &[])?.mp(base)?.mp(self)?)
        } else {
            // self: ....@x(H[x] -> H[S(x)])
            let y = gen::rename_to_avoid(&[x.to_owned()], &[&self.formula().bound().slice()])[0]
                .clone();
            let t0 = self.subst_gen(&[], &[y.clone()])?; // @y...@x(H[x] -> H[S(x)])
            let mut yboxes = vec![Boxing::Var(y.clone())];
            yboxes.extend_from_slice(boxes);
            let t1 = t0.box_subst_one(&yboxes, Expr::var(&y))?; // @y...(H[y] -> H[S(y)])
            let t2 = t1.cleave(&yboxes[0..1], yboxes.len() - 1)?; // @y(...H[y] -> ...H[S(y)])

            let boxed_hy = boxed_formula(&boxes, hx.subst(x, &Expr::var(&y))?)?;
            let t3 = Theorem::aind(boxed_hy, &y, &[])?.mp(base)?.mp(t2)?; // @y(...H[y])
            let t4 = t3.push_forall(&[], boxes.len())?; // ...@y(H[y])
            let mut boxes_x = boxes.to_vec();
            boxes_x.push(Boxing::Var(x.to_owned()));
            let t5 = t4.import(boxes.len(), &boxes_x)?; // ...@x(@y(H[y]))
            t5.box_subst_one(&boxes_x, Expr::var(x)) // ...@x(H[x])
        }
    }

    fn push_forall(self, boxes: &[Boxing], extra_depth: usize) -> Result<Self, TheoryError> {
        if extra_depth == 0 {
            return Ok(self);
        }

        let (boxes2, f) = peel_box(self.formula(), boxes.len() + 2)?;
        if &boxes2[0..boxes.len()] != boxes {
            return Err(TheoryError::BoxMismatch);
        }

        let x = match &boxes2[boxes.len()] {
            Boxing::Var(x) => x,
            _ => return Err(TheoryError::NotForAll),
        };

        match &boxes2[boxes.len() + 1] {
            Boxing::Var(y) => {
                // self: ...@x(@y(f[y]))
                let y2 = gen::rename_to_avoid(&[y.clone()], &[f.free().slice(), f.bound().slice()])
                    [0]
                .clone();
                let mut boxes_y2 = boxes.to_vec();
                boxes_y2.push(Boxing::Var(y2.clone()));
                let t0 = self.import(boxes.len(), &boxes_y2)?; // ...@y2(@x(@y(f[y])))
                let mut boxes_y2_x = boxes_y2.clone();
                boxes_y2_x.push(Boxing::Var(x.clone()));
                let t1 = Theorem::box_a6(f.clone(), y, Expr::var(&y2), &boxes_y2_x)?; // ...@y2(@x(@y(f[y]) -> f[y2]))
                let t2 = t1.box_mp(t0, &boxes_y2_x)?; // ...@y2(@x(f[y2]))
                let x_fy2 = f.subst(y, &Expr::var(&y2))?.forall(x)?;
                let mut boxes_y = boxes.to_vec();
                boxes_y.push(Boxing::Var(y.clone()));
                let t3 = t2.import(boxes.len(), &boxes_y)?; // ...@y(@y2(@x(f[y2])))
                let t4 = Theorem::box_a6(x_fy2, &y2, Expr::var(y), &boxes_y)?; // ...@y(@y2(@x(f[y2])) -> @x(f[y]))
                let t5 = t4.box_mp(t3, &boxes_y)?; // ...@y(@x(f[y]))
                t5.push_forall(&boxes_y, extra_depth - 1)
            }
            Boxing::Hyp(h) => {
                if h.free().contains(x) {
                    return Err(TheoryError::PushingPastFreeVar(x.clone()));
                }
                // self: ...@x(h -> f)
                let t0 = Theorem::box_a4(h, f, x, boxes)?.box_mp(self, boxes)?; // ...(@x(h) -> @x(f))
                let t1 = Theorem::box_a5(h, x, boxes)?; // ...(h -> @x(h))
                let t2 = t1.hyp_syllogism(t0, boxes)?; // ...(h -> @x(f))
                let mut boxes_h = boxes.to_vec();
                boxes_h.push(Boxing::Hyp(h.clone()));
                t2.push_forall(&boxes_h, extra_depth - 1)
            }
        }
    }

    fn hyp_syllogism(self, other: Self, boxes: &[Boxing]) -> Result<Self, TheoryError> {
        let ab = peel_box_exact(self.formula(), boxes)?;
        let bc = peel_box_exact(other.formula(), boxes)?;
        let (a, b) = gen::expect_imp(&ab)?;
        let (b2, c) = gen::expect_imp(&bc)?;
        if b != b2 {
            return Err(TheoryError::WrongHyp);
        }
        // self: ...(a -> b)
        // other: ...(b -> c)
        let mut boxes_plus = boxes.to_vec();
        boxes_plus.push(Boxing::Hyp((*a).clone()));
        let t0 = other.import(boxes.len(), &boxes_plus)?; // ...(a -> b -> c)
        let t1 = Theorem::box_a2(a, b, c, boxes)?; // ...((a -> b -> c) -> (a -> b) -> (a -> c))
        t1.box_mp(t0, boxes)?.box_mp(self, boxes)
    }

    fn contradiction(self, target: impl ToFormula, boxes: &[Boxing]) -> Result<Self, TheoryError> {
        // self: ...false
        let a = target.to_formula()?;
        gen::expect_false(&peel_box_exact(self.formula(), boxes)?)?;
        let t0 = Theorem::box_a3(a.clone(), boxes)?; // ...(!a -> false) -> a
        let mut boxes2 = boxes.to_vec();
        boxes2.push(Boxing::Hyp(a.not()));
        let t1 = self.import(boxes.len(), &boxes2)?; // ...(!a -> false)
        t0.box_mp(t1, boxes)
    }

    fn box_chk(&self, parseable: impl ToFormula + Clone + Debug, boxes: &[Boxing]) {
        let f = boxed_formula(boxes, parseable.clone()).unwrap();
        self.clone()
            .check(f)
            .expect(&format!("{:?} in boxes {:?}", parseable, boxes));
    }
}

pub fn boxed_formula(boxes: &[Boxing], f: impl ToFormula) -> Result<Formula, TheoryError> {
    let mut formula = f.to_formula()?;
    for b in boxes.iter().rev() {
        match b {
            Boxing::Var(x) => {
                formula = formula.forall(x)?;
            }
            Boxing::Hyp(h) => {
                formula = h.clone().imp(formula)?;
            }
        }
    }
    Ok(formula)
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
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

    pub fn push_var_and_get(&mut self, x: &str) -> Result<Expr, TheoryError> {
        self.push_var(x)?;
        Ok(Expr::var(x))
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
        for x in f.bound().slice() {
            if bounds.contains(x) {
                return Err(TheoryError::BoxHypBound(x.clone()));
            }
        }
        for x in f.free().slice() {
            if !bounds.contains(x) {
                return Err(TheoryError::BoxHypFree(x.clone()));
            }
        }
        self.0.push(Boxing::Hyp(f));
        Ok(())
    }

    /// `push_hyp`, but it returns the thing you've pushed as a theorem
    ///
    /// ```
    /// use theory::boxing::Boxes;
    ///
    /// let mut boxes = Boxes::default();
    /// let t = boxes.push_and_get("0 = 1").unwrap();
    /// t.chk("0 = 1 -> 0 = 1");
    /// ```
    pub fn push_and_get(&mut self, hyp: impl ToFormula) -> Result<Theorem, TheoryError> {
        let f = hyp.to_formula()?;
        let result = Theorem::imp_self(f.clone(), self)?;
        self.push_hyp(f)?;
        Ok(result)
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
    use kernel::pa_formula::Expr;

    fn x() -> Expr {
        Expr::var("x")
    }
    fn y() -> Expr {
        Expr::var("y")
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
