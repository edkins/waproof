use crate::boxing::TheoremBox;
use crate::eq::TheoremEq;
use crate::util::{prove, Memo};
use kernel::pa_axiom::Theorem;

#[cfg(test)]
pub mod test {
    use super::*;

    #[test]
    fn test_add() {
        add_0_r().chk("@x(x + 0 = x)");
        add_succ_r().chk("@x(@y(x + S(y) = S(x + y)))");
        add_0_l().chk("@x(0 + x = x)");
        add_succ_l().chk("@x(@y(S(x) + y = S(x + y)))");
        add_comm().chk("@x(@y(x + y = y + x))");
        add_assoc().chk("@x(@y(@z(x + (y + z) = (x + y) + z)))");
        succ_inj().chk("@x(@y(S(x) = S(y) -> x = y))");
        add_cancel_r().chk("@x(@y(@z(x + z = y + z -> x = y)))");
        add_cancel_l().chk("@x(@y(@z(x + y = x + z -> y = z)))");
    }
}

pub fn add_0_r() -> Theorem {
    Theorem::aa1()
}

pub fn add_succ_r() -> Theorem {
    Theorem::aa2()
}

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

pub fn add_assoc() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove(&RESULT, |mut boxes| {
        boxes.push_var("x")?;
        boxes.push_var("y")?;
        boxes.push_var("z")?;
        let ih = boxes.push_and_get("x + (y + z) = (x + y) + z")?;

        // Inductive step
        let ti = boxes
            .chain("x + (y + S(z))")?
            .equals("x + S(y + z)", add_succ_r())?
            .equals("S(x + (y + z))", add_succ_r())?
            .equals("S((x + y) + z)", ih)?
            .equals("(x + y) + S(z)", add_succ_r())?;
        boxes.pop()?;
        boxes.pop()?;

        // Base case
        let t0 = boxes
            .chain("x + (y + 0)")?
            .equals("x + y", add_0_r())?
            .equals("(x + y) + 0", add_0_r())?;

        ti.induction(t0, &boxes)
    })
}

pub fn succ_inj() -> Theorem {
    Theorem::as2()
}


pub fn add_cancel_r() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove(&RESULT, |mut boxes| {
        boxes.push_var("x")?;
        boxes.push_var("y")?;
        boxes.push_var("z")?;
        let ih = boxes.push_and_get("x + z = y + z -> x = y")?;

        // Inductive step
        let t1 = boxes.push_and_get("x + S(z) = y + S(z)")?;
        let t2 = boxes
            .chain("S(x + z)")?
            .equals("x + S(z)", add_succ_r())?
            .equals("y + S(z)", t1)?
            .equals("S(y + z)", add_succ_r())?;
        let t3 = succ_inj().import_subst(&boxes, &["x + z", "y + z"])?;
        let t4 = t3.box_mp(t2, &boxes)?;
        t4.box_chk("x + z = y + z", &boxes);
        let ti = ih.import(4, &boxes)?.box_mp(t4, &boxes)?;
        boxes.pop()?;
        boxes.pop()?;
        boxes.pop()?;

        // Base case
        let t5 = boxes.push_and_get("x + 0 = y + 0")?;
        let t0 = boxes
            .chain("x")?
            .equals("x + 0", add_0_r())?
            .equals("y + 0", t5)?
            .equals("y", add_0_r())?;
        boxes.pop()?;

        ti.induction(t0, &boxes)
    })
}

pub fn add_cancel_l() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove(&RESULT, |mut boxes| {
        boxes.push_var("x")?;
        boxes.push_var("y")?;
        boxes.push_var("z")?;
        let t0 = boxes.push_and_get("x + y = x + z")?;
        let t1 = boxes
            .chain("y + x")?
            .equals("x + y", add_comm())?
            .equals("x + z", t0)?
            .equals("z + x", add_comm())?;
        let t2 = add_cancel_r().import_subst(&boxes, &["y","z","x"])?;
        t2.box_mp(t1, &boxes)
    })
}
