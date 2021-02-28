use crate::boxing::{Boxes, TheoremBox};
use crate::eq::TheoremEq;
use kernel::pa_axiom::Theorem;

/// ```
/// use theory::add::add_0_r;
/// use theory::gen::TheoremGen;
///
/// add_0_r().check("@x(x + 0 = x)").unwrap();
/// ```
pub fn add_0_r() -> Theorem {
    Theorem::aa1()
}

/// ```
/// use theory::add::add_succ_r;
/// use theory::gen::TheoremGen;
///
/// add_succ_r().check("@x(@y(x + S(y) = S(x + y)))").unwrap();
/// ```
pub fn add_succ_r() -> Theorem {
    Theorem::aa2()
}

/// ```
/// use theory::add::add_0_l;
/// use theory::gen::TheoremGen;
///
/// add_0_l().check("@x(0 + x = x)").unwrap();
/// ```
pub fn add_0_l() -> Theorem {
    let mut boxes = Boxes::default();
    boxes.push_var("x").unwrap();
    let eq = boxes.push_and_get("0 + x = x").unwrap();
    let t0 = add_succ_r().import_subst(&boxes, &["0", "x"]).unwrap();
    t0.chk("@x(0 + x = x -> 0 + S(x) = S(0 + x))");
    let t1 = t0.eq_subst(eq, "0 + S(x) = S(x)", &boxes).unwrap();
    t1.chk("@x(0 + x = x -> 0 + S(x) = S(x))");
    boxes.pop().unwrap();
    boxes.pop().unwrap();
    let t2 = add_0_r().import_subst(&boxes, &["0"]).unwrap();
    t2.chk("0 + 0 = 0");
    t1.induction(t2, &boxes).unwrap()
}
