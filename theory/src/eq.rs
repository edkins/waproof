use crate::boxing::{self, TheoremBox};
use crate::equalizer::Equalizer;
use crate::util::TheoryError;
use kernel::pa_axiom::Theorem;
use kernel::pa_parse::ToExpr;

pub trait TheoremEq: Sized {
    // Try to prove `target`, by taking the current theorem and substituting things that
    // are equal. Operates inside a box, i.e. the equality might be conditional on some
    // hypotheses.
    //
    // `target` does not include the boxed stuff.
    //
    // ```
    // use kernel::pa_axiom::Theorem;
    // use theory::boxing::TheoremBox;
    // use theory::eq::TheoremEq;
    //
    // let t0 = Theorem::aa1().import_subst(&[], &["0"]).unwrap();
    // t0.chk("0 + 0 = 0");
    // let t1 = Theorem::as1().import_subst(&[], &["0"]).unwrap();
    // t1.chk("!(0 = S(0))");
    // let t2 = t1.eq_subst(t0, "!(0 = S(0+0))", &[]).unwrap();
    // t2.chk("!(0 = S(0+0))");
    // ```
    /*fn eq_subst(
        self,
        equality: Self,
        target: impl ToFormula,
        boxes: &[Boxing],
    ) -> Result<Self, TheoryError>;*/

    /// Assumes that self is a boxed equality. Aims to prove our RHS = target.
    fn equals(self, target: impl ToExpr, equalizer: impl Equalizer) -> Result<Self, TheoryError>;

    fn eq_swap(self) -> Result<Self, TheoryError>;
}

impl TheoremEq for Theorem {
    fn equals(self, target: impl ToExpr, equalizer: impl Equalizer) -> Result<Self, TheoryError> {
        let (boxes, left, right) = boxing::peel_box_until_eq(&self.formula())?;
        let target = target.into_expr()?;
        let t1 = equalizer.prove_eq(&right, &target, &boxes)?;
        let t2 = Theorem::ae3().import_subst(&boxes, &[left, right, target])?;
        t2.box_mp(self, &boxes)?.box_mp(t1, &boxes)
    }

    fn eq_swap(self) -> Result<Self, TheoryError> {
        let (boxes, left, right) = boxing::peel_box_until_eq(&self.formula())?;
        let t0 = Theorem::ae2().import_subst(&boxes, &[left, right])?;
        t0.box_mp(self, &boxes)
    }
}

/*
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
*/
