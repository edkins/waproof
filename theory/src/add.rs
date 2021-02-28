use crate::boxing::{Boxes, TheoremBox};
use crate::eq::TheoremEq;
use kernel::pa_axiom::Theorem;
use std::cell::RefCell;

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
        static RESULT: RefCell<Option<Theorem>> = RefCell::new(None);
    }
    RESULT.with(|r| {
        r.borrow_mut()
            .get_or_insert_with(|| {
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
            })
            .clone()
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
        static RESULT: RefCell<Option<Theorem>> = RefCell::new(None);
    }
    RESULT.with(|r| {
        r.borrow_mut()
            .get_or_insert_with(|| {
                let mut boxes = Boxes::default();
                boxes.push_var("x").unwrap();
                boxes.push_var("y").unwrap();
                let eq = boxes.push_and_get("S(x) + y = S(x + y)").unwrap();
                let t0 = add_succ_r().import_subst(&boxes, &["S(x)", "y"]).unwrap();
                t0.box_chk("S(x) + S(y) = S(S(x) + y)", &boxes);
                let t1 = t0
                    .eq_subst(eq, "S(x) + S(y) = S(S(x + y))", &boxes)
                    .unwrap();
                let t2 = add_succ_r().import_subst(&boxes, &["x", "y"]).unwrap();
                t2.box_chk("x + S(y) = S(x + y)", &boxes);
                let t3 = t1
                    .eq_subst(t2, "S(x) + S(y) = S(x + S(y))", &boxes)
                    .unwrap();
                boxes.pop().unwrap();
                boxes.pop().unwrap();
                let t4 = add_0_r().import_subst(&boxes, &["S(x)"]).unwrap();
                t4.box_chk("S(x) + 0 = S(x)", &boxes);
                let t5 = add_0_r().import_subst(&boxes, &["x"]).unwrap();
                t5.box_chk("x + 0 = x", &boxes);
                let t6 = t4.eq_subst(t5, "S(x) + 0 = S(x + 0)", &boxes).unwrap();
                t3.induction(t6, &boxes).unwrap()
            })
            .clone()
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
        static RESULT: RefCell<Option<Theorem>> = RefCell::new(None);
    }
    RESULT.with(|r| {
        r.borrow_mut()
            .get_or_insert_with(|| {
                let mut boxes = Boxes::default();
                boxes.push_var("x").unwrap();
                boxes.push_var("y").unwrap();
                let ih = boxes.push_and_get("x + y = y + x").unwrap();

                // Inductive step
                let t0 = add_succ_r().import_subst(&boxes, &["x", "y"]).unwrap();
                t0.box_chk("x + S(y) = S(x + y)", &boxes);

                let t1 = t0.eq_subst(ih, "x + S(y) = S(y + x)", &boxes).unwrap();

                let t2 = add_succ_l().import_subst(&boxes, &["y", "x"]).unwrap();
                t2.box_chk("S(y) + x = S(y + x)", &boxes);

                let t3 = t1.eq_subst(t2, "x + S(y) = S(y) + x", &boxes).unwrap();
                boxes.pop().unwrap();
                boxes.pop().unwrap();

                // Base case
                let t4 = add_0_r().import_subst(&boxes, &["x"]).unwrap();
                t4.box_chk("x + 0 = x", &boxes);

                let t5 = add_0_l().import_subst(&boxes, &["x"]).unwrap();
                t5.box_chk("0 + x = x", &boxes);

                let t6 = t4.eq_subst(t5, "x + 0 = 0 + x", &boxes).unwrap();

                t3.induction(t6, &boxes).unwrap()
            })
            .clone()
    })
}
