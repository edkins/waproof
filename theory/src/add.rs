use crate::boxing::{Boxes, TheoremBox};
use crate::eq::TheoremEq;
use crate::util::{prove, Memo};
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
/// add_0_l().chk("@x(0 + x = x)");
/// ```
pub fn add_0_l() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove(&RESULT, || {
        let mut boxes = Boxes::default();
        boxes.push_var("x")?;
        let eq = boxes.push_and_get("0 + x = x")?;
        let t0 = add_succ_r().import_subst(&boxes, &["0", "x"])?;
        t0.chk("@x(0 + x = x -> 0 + S(x) = S(0 + x))");
        let t1 = t0.eq_subst(eq, "0 + S(x) = S(x)", &boxes)?;
        t1.chk("@x(0 + x = x -> 0 + S(x) = S(x))");
        boxes.pop()?;
        boxes.pop()?;
        let t2 = add_0_r().import_subst(&boxes, &["0"])?;
        t2.chk("0 + 0 = 0");
        t1.induction(t2, &boxes)
    })
}

/// ```
/// use theory::add::add_succ_l;
/// use theory::gen::TheoremGen;
///
/// add_succ_l().chk("@x(@y(S(x) + y = S(x + y)))");
/// ```
pub fn add_succ_l() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove(&RESULT, || {
        let mut boxes = Boxes::default();
        boxes.push_var("x")?;
        boxes.push_var("y")?;
        let eq = boxes.push_and_get("S(x) + y = S(x + y)")?;
        let t0 = add_succ_r().import_subst(&boxes, &["S(x)", "y"])?;
        t0.box_chk("S(x) + S(y) = S(S(x) + y)", &boxes);
        let t1 = t0.eq_subst(eq, "S(x) + S(y) = S(S(x + y))", &boxes)?;
        let t2 = add_succ_r().import_subst(&boxes, &["x", "y"])?;
        t2.box_chk("x + S(y) = S(x + y)", &boxes);
        let t3 = t1.eq_subst(t2, "S(x) + S(y) = S(x + S(y))", &boxes)?;
        boxes.pop()?;
        boxes.pop()?;
        let t4 = add_0_r().import_subst(&boxes, &["S(x)"])?;
        t4.box_chk("S(x) + 0 = S(x)", &boxes);
        let t5 = add_0_r().import_subst(&boxes, &["x"])?;
        t5.box_chk("x + 0 = x", &boxes);
        let t6 = t4.eq_subst(t5, "S(x) + 0 = S(x + 0)", &boxes)?;
        t3.induction(t6, &boxes)
    })
}

/// ```
/// use theory::add::add_comm;
/// use theory::gen::TheoremGen;
///
/// add_comm().chk("@x(@y(x + y = y + x))");
/// ```
pub fn add_comm() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove(&RESULT, || {
        let mut boxes = Boxes::default();
        boxes.push_var("x")?;
        boxes.push_var("y")?;
        let ih = boxes.push_and_get("x + y = y + x")?;

        // Inductive step
        let t0 = add_succ_r().import_subst(&boxes, &["x", "y"])?;
        t0.box_chk("x + S(y) = S(x + y)", &boxes);

        let t1 = t0.eq_subst(ih, "x + S(y) = S(y + x)", &boxes)?;

        let t2 = add_succ_l().import_subst(&boxes, &["y", "x"])?;
        t2.box_chk("S(y) + x = S(y + x)", &boxes);

        let t3 = t1.eq_subst(t2, "x + S(y) = S(y) + x", &boxes)?;
        boxes.pop()?;
        boxes.pop()?;

        // Base case
        let t4 = add_0_r().import_subst(&boxes, &["x"])?;
        t4.box_chk("x + 0 = x", &boxes);

        let t5 = add_0_l().import_subst(&boxes, &["x"])?;
        t5.box_chk("0 + x = x", &boxes);

        let t6 = t4.eq_subst(t5, "x + 0 = 0 + x", &boxes)?;

        t3.induction(t6, &boxes)
    })
}
