use crate::boxing::{self, Boxing, TheoremBox};
use crate::equalizer::Equalizer;
use crate::util::TheoryError;
use kernel::pa_axiom::Theorem;
use kernel::pa_formula::{Expr, Formula};
use kernel::pa_parse::{ToExpr, ToFormula};

pub trait TheoremEq: Sized {
    /// Try to prove `target`, by taking the current theorem and substituting things that
    /// are equal. Operates inside a box, i.e. the equality might be conditional on some
    /// hypotheses.
    ///
    /// `target` does not include the boxed stuff.
    ///
    /// ```
    /// use kernel::pa_axiom::Theorem;
    /// use theory::boxing::TheoremBox;
    /// use theory::eq::TheoremEq;
    ///
    /// let t0 = Theorem::aa1().import_subst(&[], &["0"]).unwrap();
    /// t0.chk("0 + 0 = 0");
    /// let t1 = Theorem::as1().import_subst(&[], &["0"]).unwrap();
    /// t1.chk("!(0 = S(0))");
    /// let t2 = t1.eq_subst(t0, "!(0 = S(0+0))", &[]).unwrap();
    /// t2.chk("!(0 = S(0+0))");
    /// ```
    fn eq_subst(
        self,
        equality: Self,
        target: impl ToFormula,
        boxes: &[Boxing],
    ) -> Result<Self, TheoryError>;

    /// Assumes that self is a boxed equality. Aims to prove our RHS = target.
    fn equals(self, target: impl ToExpr, equalizer: impl Equalizer) -> Result<Self, TheoryError>;
}

// Aim to prove left = right
fn eq_subst_exp(
    left: &Expr,
    right: &Expr,
    equality: &Theorem,
    eq_left: &Expr,
    eq_right: &Expr,
    boxes: &[Boxing],
) -> Result<Theorem, TheoryError> {
    if left == right {
        let t1 = Theorem::ae1(); // @x(x = x)
        t1.import_subst(boxes, &[left])
    } else if left == eq_left && right == eq_right {
        Ok(equality.clone())
    } else if left == eq_right && right == eq_left {
        let t1 = Theorem::ae2(); // @x(@y(x = y -> y = x))
        t1.import_subst(boxes, &[eq_left, eq_right])?
            .box_mp(equality.clone(), boxes)
    } else {
        match (left, right) {
            (Expr::S(a), Expr::S(b)) => {
                let ab = eq_subst_exp(a, b, equality, eq_left, eq_right, boxes)?;
                let t1 = Theorem::aes(); // @x(@y(x = y -> S(x) = S(y)))
                t1.import_subst(boxes, &[a, b])?.box_mp(ab, boxes)
            }
            (Expr::Add(a, c), Expr::Add(b, d)) => {
                if a == b {
                    let cd = eq_subst_exp(&**c, &**d, equality, eq_left, eq_right, boxes)?; // c = d
                    let t1 = Theorem::aea2(); // @x(@y(@z(y = z -> x + y = x + z)))
                    t1.import_subst(boxes, &[a, c, d])?.box_mp(cd, boxes)
                } else if c == d {
                    let ab = eq_subst_exp(&**a, &**b, equality, eq_left, eq_right, boxes)?; // a = b
                    let t1 = Theorem::aea1(); // @x(@y(@z(x = y -> x + z = y + z)))
                    t1.import_subst(boxes, &[a, b, c])?.box_mp(ab, boxes)
                } else {
                    let ab = eq_subst_exp(&**a, &**b, equality, eq_left, eq_right, boxes)?; // a = b
                    let cd = eq_subst_exp(&**c, &**d, equality, eq_left, eq_right, boxes)?; // c = d
                    let t1 = Theorem::aea2(); // @x(@y(@z(y = z -> x + y = x + z)))
                    let t2 = t1.import_subst(boxes, &[a, c, d])?.box_mp(cd, boxes)?; // a + c = a + d
                    let t3 = Theorem::aea1(); // @x(@y(@z(x = y -> x + z = y + z)))
                    let t4 = t3.import_subst(boxes, &[a, b, d])?.box_mp(ab, boxes)?; // a + d = b + d
                    let t5 = Theorem::ae3(); // @x(@y(@z(x = y -> y = z -> x = z)))
                    t5.import_subst(
                        boxes,
                        &[
                            Expr::Add(a.clone(), c.clone()),
                            Expr::Add(a.clone(), d.clone()),
                            Expr::Add(b.clone(), d.clone()),
                        ],
                    )?
                    .box_mp(t2, boxes)?
                    .box_mp(t4, boxes)
                }
            }
            (Expr::Mul(a, c), Expr::Mul(b, d)) => {
                if a == b {
                    let cd = eq_subst_exp(&**c, &**d, equality, eq_left, eq_right, boxes)?; // c = d
                    let t1 = Theorem::aem2(); // @x(@y(@z(y = z -> x * y = x * z)))
                    t1.import_subst(boxes, &[a, c, d])?.box_mp(cd, boxes)
                } else if c == d {
                    let ab = eq_subst_exp(&**a, &**b, equality, eq_left, eq_right, boxes)?; // a = b
                    let t1 = Theorem::aem1(); // @x(@y(@z(x = y -> x * z = y * z)))
                    t1.import_subst(boxes, &[a, b, c])?.box_mp(ab, boxes)
                } else {
                    let ab = eq_subst_exp(&**a, &**b, equality, eq_left, eq_right, boxes)?; // a = b
                    let cd = eq_subst_exp(&**c, &**d, equality, eq_left, eq_right, boxes)?; // c = d
                    let t1 = Theorem::aem2(); // @x(@y(@z(y = z -> x * y = x * z)))
                    let t2 = t1.import_subst(boxes, &[a, c, d])?.box_mp(cd, boxes)?; // a * c = a * d
                    let t3 = Theorem::aem1(); // @x(@y(@z(x = y -> x * z = y * z)))
                    let t4 = t3.import_subst(boxes, &[a, b, d])?.box_mp(ab, boxes)?; // a * d = b * d
                    let t5 = Theorem::ae3(); // @x(@y(@z(x = y -> y = z -> x = z)))
                    t5.import_subst(
                        boxes,
                        &[
                            Expr::Mul(a.clone(), c.clone()),
                            Expr::Mul(a.clone(), d.clone()),
                            Expr::Mul(b.clone(), d.clone()),
                        ],
                    )?
                    .box_mp(t2, boxes)?
                    .box_mp(t4, boxes)
                }
            }
            _ => Err(TheoryError::StructuralMismatch),
        }
    }
}

// Aim to prove source -> target
fn eq_subst_rec(
    source: &Formula,
    target: &Formula,
    equality: &Theorem,
    eq_left: &Expr,
    eq_right: &Expr,
    boxes: &[Boxing],
) -> Result<Theorem, TheoryError> {
    if source == target {
        Theorem::imp_self(source, boxes)
    } else {
        match (source, target) {
            (Formula::Eq(a, c), Formula::Eq(b, d)) => {
                if c == d {
                    let ba = eq_subst_exp(b, a, equality, eq_left, eq_right, boxes)?; // b = a
                    let t1 = Theorem::ae3(); // @x(@y(@z(x = y -> y = z -> x = z)))
                    t1.import_subst(boxes, &[b, a, c])?.box_mp(ba, boxes)
                } else if a == b {
                    let cd = eq_subst_exp(c, d, equality, eq_left, eq_right, boxes)?; // c = d
                    let t1 = Theorem::ae3(); // @x(@y(@z(x = y -> y = z -> x = z)))
                    let t2 = t1.import_subst(boxes, &[a, c, d])?; // a = c -> c = d -> b = d      because a == b
                    let mut boxes_plus = boxes.to_vec();
                    boxes_plus.push(Boxing::Hyp(a.reconstitute().eq(c.reconstitute())));
                    let t3 = cd.import(boxes.len(), &boxes_plus)?; // a = c -> c = d
                    t2.box_mp(t3, &boxes_plus)
                } else {
                    let cd = eq_subst_exp(c, d, equality, eq_left, eq_right, boxes)?; // c = d
                    let t1 = Theorem::ae3(); // @x(@y(@z(x = y -> y = z -> x = z)))
                    let t2 = t1.clone().import_subst(boxes, &[a, c, d])?; // (a = c) -> c = d -> a = d
                    let mut boxes_plus = boxes.to_vec();
                    boxes_plus.push(Boxing::Hyp(a.reconstitute().eq(c.reconstitute())));
                    let tcd = cd.import(boxes.len(), &boxes_plus)?; // (a = c) -> c = d
                    let t3 = t2.box_mp(tcd, &boxes_plus)?; // (a = c) -> a = d
                    let t4 = t1.import_subst(&boxes_plus, &[b, a, d])?; // (a = c) -> b = a -> a = d -> b = d
                    let ba = eq_subst_exp(b, a, equality, eq_left, eq_right, &boxes)?; // b = a
                    let t5 = ba.import(boxes.len(), &boxes_plus)?; // (a = c) -> b = a
                    t4.box_mp(t5, &boxes_plus)?.box_mp(t3, &boxes_plus)
                }
            }
            (Formula::Imp(a, c), Formula::Imp(b, d)) => {
                if a == b {
                    let mut boxes_plus = boxes.to_vec();
                    boxes_plus.push(Boxing::Hyp(a.reconstitute()?));
                    let cd = eq_subst_rec(c, d, equality, eq_left, eq_right, boxes)?; // (c -> d)
                    let t0 = cd.import(boxes.len(), &boxes_plus)?; // a -> (c -> d)
                    let t1 = Theorem::box_a2(a, c, d, boxes)?; // (a -> (c -> d)) -> (a -> c) -> (b -> d)   because a == b
                    t1.box_mp(t0, &boxes)
                } else if c == d {
                    let t1 = Theorem::box_a1(source, b, boxes)?; // (a -> c) -> (b -> a -> c)
                    let mut boxes_plus = boxes.to_vec();
                    boxes_plus.push(Boxing::Hyp(source.reconstitute()?));
                    let t2 = Theorem::box_a2(b, a, c, &boxes_plus)?; // (a -> c) -> (b -> a -> c) -> (b -> a) -> (b -> d)  because c == d
                    let t3 = t2.box_mp(t1, &boxes_plus)?; // (a -> c) -> (b -> a) -> (b -> d)
                    let ba = eq_subst_rec(b, a, equality, eq_left, eq_right, boxes)?; // b -> a
                    let t4 = ba.import(boxes.len(), &boxes_plus)?; // (a -> c) -> (b -> a)
                    t3.box_mp(t4, &boxes_plus)
                } else {
                    let t1 = Theorem::box_a1(source, b, boxes)?; // (a -> c) -> (b -> a -> c)
                    let mut boxes_plus = boxes.to_vec();
                    boxes_plus.push(Boxing::Hyp(source.reconstitute()?));
                    let t2 = Theorem::box_a2(b, a, c, &boxes_plus)?; // (a -> c) -> (b -> a -> c) -> (b -> a) -> (b -> c)
                    let t3 = t2.box_mp(t1, &boxes_plus)?; // (a -> c) -> (b -> a) -> (b -> c)
                    let ba = eq_subst_rec(b, a, equality, eq_left, eq_right, boxes)?; // b -> a
                    let t4 = ba.import(boxes.len(), &boxes_plus)?; // (a -> c) -> (b -> a)
                    let t5 = t3.box_mp(t4, &boxes_plus)?; // (a -> c) -> b -> c
                    let cd = eq_subst_rec(c, d, equality, eq_left, eq_right, boxes)?; // c -> d
                    boxes_plus.push(Boxing::Hyp(b.reconstitute()?));
                    let t6 = cd.import(boxes.len(), &boxes_plus)?; // (a -> c) -> b -> (c -> d)
                    t6.box_mp(t5, &boxes_plus)
                }
            }
            (Formula::ForAll(x, c), Formula::ForAll(y, d)) => {
                if x == y {
                    let cd = eq_subst_rec(c, d, equality, eq_left, eq_right, boxes)?;
                    let mut boxes_plus = boxes.to_vec();
                    boxes_plus.push(Boxing::Var(x.clone()));
                    let t0 = cd.import(boxes.len(), &boxes_plus)?; // @x(c -> d)
                    let t1 = Theorem::box_a4(c, d, x, boxes)?; // @x(c -> d) -> @x(c) -> @x(d)
                    t1.box_mp(t0, &boxes)
                } else {
                    Err(TheoryError::StructuralMismatch)
                }
            }
            _ => Err(TheoryError::StructuralMismatch),
        }
    }
}

impl TheoremEq for Theorem {
    fn eq_subst(
        self,
        equality: Self,
        target: impl ToFormula,
        boxes: &[Boxing],
    ) -> Result<Self, TheoryError> {
        let eqf = boxing::peel_box_exact(equality.formula(), boxes)?;
        let sourcef = boxing::peel_box_exact(self.formula(), boxes)?;
        let targetf = target.to_formula()?;
        let (eq_left, eq_right) = match eqf.formula() {
            Formula::Eq(a, b) => (a, b),
            _ => return Err(TheoryError::NotEquality),
        };
        eq_subst_rec(
            sourcef.formula(),
            targetf.formula(),
            &equality,
            &*eq_left,
            &*eq_right,
            boxes,
        )?
        .box_mp(self, boxes)
    }

    fn equals(self, target: impl ToExpr, equalizer: impl Equalizer) -> Result<Self, TheoryError> {
        let (boxes, left, right) = boxing::peel_box_until_eq(&self.formula())?;
        let target = target.to_expr()?.expr().clone();
        let t1 = equalizer.prove_eq(&right, &target, &boxes)?;
        let t2 = Theorem::ae3().import_subst(&boxes, &[left, right, target])?;
        t2.box_mp(self, &boxes)?.box_mp(t1, &boxes)
    }
}

#[cfg(test)]
mod test {
    use super::TheoremEq;
    use crate::boxing::{Boxes, TheoremBox};
    use kernel::pa_axiom::Theorem;

    #[test]
    fn s_eq_r() {
        let mut boxes = Boxes::default();
        boxes.push_var("x").unwrap();
        boxes.push_var("y").unwrap();
        let eq = Theorem::imp_self("x = y", &boxes).unwrap();
        eq.chk("@x(@y(x = y -> x = y))");
        boxes.push_hyp("x = y").unwrap();
        let t0 = Theorem::ae1();
        t0.chk("@x(x = x)");
        let t1 = t0.import_subst(&boxes, &["S(y)"]).unwrap();
        t1.chk("@x(@y(x = y -> S(y) = S(y)))");
        let t2 = t1.eq_subst(eq, "S(y) = S(x)", &boxes).unwrap();
        t2.chk("@x(@y(x = y -> S(y) = S(x)))");
    }

    #[test]
    fn eq_l() {
        let mut boxes = Boxes::default();
        boxes.push_var("x").unwrap();
        boxes.push_var("y").unwrap();
        let eq = Theorem::imp_self("x = y", &boxes).unwrap();
        eq.chk("@x(@y(x = y -> x = y))");
        boxes.push_hyp("x = y").unwrap();
        let t0 = Theorem::ae1();
        t0.chk("@x(x = x)");
        let t1 = t0.import_subst(&boxes, &["S(y)"]).unwrap();
        t1.chk("@x(@y(x = y -> S(y) = S(y)))");
        let t2 = t1.eq_subst(eq, "S(x) = S(y)", &boxes).unwrap();
        t2.chk("@x(@y(x = y -> S(x) = S(y)))");
    }

    #[test]
    fn eq_both() {
        let mut boxes = Boxes::default();
        boxes.push_var("x").unwrap();
        boxes.push_var("y").unwrap();
        let eq = Theorem::imp_self("x = y", &boxes).unwrap();
        eq.chk("@x(@y(x = y -> x = y))");
        boxes.push_hyp("x = y").unwrap();
        let t0 = Theorem::ae1();
        t0.chk("@x(x = x)");
        let t1 = t0.import_subst(&boxes, &["S(y)"]).unwrap();
        t1.chk("@x(@y(x = y -> S(y) = S(y)))");
        let t2 = t1.eq_subst(eq, "S(x) = S(x)", &boxes).unwrap();
        t2.chk("@x(@y(x = y -> S(x) = S(x)))");
    }

    #[test]
    fn add_l() {
        let mut boxes = Boxes::default();
        boxes.push_var("x").unwrap();
        boxes.push_var("y").unwrap();
        let eq = Theorem::imp_self("x = y", &boxes).unwrap();
        eq.chk("@x(@y(x = y -> x = y))");
        boxes.push_hyp("x = y").unwrap();
        let t0 = Theorem::aa1();
        t0.chk("@x(x + 0 = x)");
        let t1 = t0.import_subst(&boxes, &["x"]).unwrap();
        t1.chk("@x(@y(x = y -> x + 0 = x))");
        let t2 = t1.eq_subst(eq, "y + 0 = x", &boxes).unwrap();
        t2.chk("@x(@y(x = y -> y + 0 = x))");
    }

    #[test]
    fn add_r() {
        let mut boxes = Boxes::default();
        boxes.push_var("x").unwrap();
        let eq = Theorem::imp_self("x = 0", &boxes).unwrap();
        eq.chk("@x(x = 0 -> x = 0)");
        boxes.push_hyp("x = 0").unwrap();
        let t0 = Theorem::aa1();
        t0.chk("@x(x + 0 = x)");
        let t1 = t0.import_subst(&boxes, &["x"]).unwrap();
        t1.chk("@x(x = 0 -> x + 0 = x)");
        let t2 = t1.eq_subst(eq, "x + x = x", &boxes).unwrap();
        t2.chk("@x(x = 0 -> x + x = x)");
    }

    #[test]
    fn add_both() {
        let mut boxes = Boxes::default();
        boxes.push_var("x").unwrap();
        let eq = Theorem::imp_self("x = 0", &boxes).unwrap();
        eq.chk("@x(x = 0 -> x = 0)");
        boxes.push_hyp("x = 0").unwrap();
        let t0 = Theorem::aa1();
        t0.chk("@x(x + 0 = x)");
        let t1 = t0.import_subst(&boxes, &["x"]).unwrap();
        t1.chk("@x(x = 0 -> x + 0 = x)");
        let t2 = t1.eq_subst(eq, "0 + x = x", &boxes).unwrap();
        t2.chk("@x(x = 0 -> 0 + x = x)");
    }

    #[test]
    fn mul_l() {
        let mut boxes = Boxes::default();
        boxes.push_var("x").unwrap();
        boxes.push_var("y").unwrap();
        let eq = Theorem::imp_self("x = y", &boxes).unwrap();
        eq.chk("@x(@y(x = y -> x = y))");
        boxes.push_hyp("x = y").unwrap();
        let t0 = Theorem::am1();
        t0.chk("@x(x * 0 = 0)");
        let t1 = t0.import_subst(&boxes, &["x"]).unwrap();
        t1.chk("@x(@y(x = y -> x * 0 = 0))");
        let t2 = t1.eq_subst(eq, "y * 0 = 0", &boxes).unwrap();
        t2.chk("@x(@y(x = y -> y * 0 = 0))");
    }

    #[test]
    fn mul_r() {
        let mut boxes = Boxes::default();
        boxes.push_var("x").unwrap();
        let eq = Theorem::imp_self("x = 0", &boxes).unwrap();
        eq.chk("@x(x = 0 -> x = 0)");
        boxes.push_hyp("x = 0").unwrap();
        let t0 = Theorem::am1();
        t0.chk("@x(x * 0 = 0)");
        let t1 = t0.import_subst(&boxes, &["x"]).unwrap();
        t1.chk("@x(x = 0 -> x * 0 = 0)");
        let t2 = t1.eq_subst(eq, "x * x = 0", &boxes).unwrap();
        t2.chk("@x(x = 0 -> x * x = 0)");
    }

    #[test]
    fn mul_both() {
        let mut boxes = Boxes::default();
        boxes.push_var("x").unwrap();
        let eq = Theorem::imp_self("x = 0", &boxes).unwrap();
        eq.chk("@x(x = 0 -> x = 0)");
        boxes.push_hyp("x = 0").unwrap();
        let t0 = Theorem::am1();
        t0.chk("@x(x * 0 = 0)");
        let t1 = t0.import_subst(&boxes, &["x"]).unwrap();
        t1.chk("@x(x = 0 -> x * 0 = 0)");
        let t2 = t1.eq_subst(eq, "0 * x = 0", &boxes).unwrap();
        t2.chk("@x(x = 0 -> 0 * x = 0)");
    }

    #[test]
    fn forall() {
        let mut boxes = Boxes::default();
        boxes.push_var("x").unwrap();
        let eq = Theorem::imp_self("x = 0", &boxes).unwrap();
        eq.chk("@x(x = 0 -> x = 0)");
        boxes.push_hyp("x = 0").unwrap();
        boxes.push_var("y").unwrap();
        let t0 = Theorem::aa1().import_subst(&boxes, &["x"]).unwrap();
        t0.chk("@x(x = 0 -> @y(x + 0 = x))");
        boxes.pop().unwrap();
        let t1 = t0.eq_subst(eq, "@y(0 + 0 = x)", &boxes).unwrap();
        t1.chk("@x(x = 0 -> @y(0 + 0 = x))");
    }
}
