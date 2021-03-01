use crate::boxing::TheoremBox;
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
    prove(&RESULT, |mut boxes| {
        boxes.push_var("x")?;
        let ih = boxes.push_and_get("0 + x = x")?;

        // Inductive step
        let ti = boxes
            .chain("0 + S(x)")?
            .equals("S(0 + x)", add_succ_r())?
            .equals("S(x)", ih)?;
        boxes.pop()?;
        boxes.pop()?;

        let t0 = boxes.chain("0 + 0")?.equals("0", add_0_r())?;

        ti.induction(t0, &boxes)
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
    prove(&RESULT, |mut boxes| {
        boxes.push_var("x")?;
        boxes.push_var("y")?;
        let ih = boxes.push_and_get("S(x) + y = S(x + y)")?;

        // Inductive step
        let ti = boxes
            .chain("S(x) + S(y)")?
            .equals("S(S(x) + y)", add_succ_r())?
            .equals("S(S(x + y))", ih)?
            .equals("S(x + S(y))", add_succ_r())?;
        boxes.pop()?;
        boxes.pop()?;

        // Base case
        let t0 = boxes
            .chain("S(x) + 0")?
            .equals("S(x)", add_0_r())?
            .equals("S(x + 0)", add_0_r())?;

        ti.induction(t0, &boxes)
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
    prove(&RESULT, |mut boxes| {
        boxes.push_var("x")?;
        boxes.push_var("y")?;
        let ih = boxes.push_and_get("x + y = y + x")?;

        // Inductive step
        let ti = boxes
            .chain("x + S(y)")?
            .equals("S(x + y)", add_succ_r())?
            .equals("S(y + x)", ih)?
            .equals("S(y) + x", add_succ_l())?;

        boxes.pop()?;
        boxes.pop()?;

        // Base case
        let t0 = boxes
            .chain("x + 0")?
            .equals("x", add_0_r())?
            .equals("0 + x", add_0_l())?;

        ti.induction(t0, &boxes)
    })
}
