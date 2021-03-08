use crate::boxing::TheoremBox;
use crate::eq::TheoremEq;
use crate::util::{prove, prove_with_script, Memo};
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
        eq_add_0_r().chk("@x(@y(x + y = 0 -> y = 0))");
        neq_0_succ().chk("@x(!(0 = S(x)))");
    }
}

pub fn add_0_r() -> Theorem {
    Theorem::aa1()
}

pub fn add_succ_r() -> Theorem {
    Theorem::aa2()
}

fn add_0_l() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove_with_script(
        &RESULT,
        "
var x
{
    hyp 0 + x = x
    {
        chain 0 + S(x) = S(0 + x) = S(x);
    }
}
chain 0 + 0 = 0;
induction;
",
        &[add_succ_r(), add_0_r()],
    )
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
        let t2 = add_cancel_r().import_subst(&boxes, &["y", "z", "x"])?;
        t2.box_mp(t1, &boxes)
    })
}

pub fn eq_add_0_r() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove(&RESULT, |mut boxes| {
        boxes.push_var("x")?;
        boxes.push_var("y")?;
        let _ih = boxes.push_and_get("x + y = 0 -> y = 0")?;

        let hyp = boxes.push_and_get("x + S(y) = 0")?;
        let t1 = boxes
            .chain("0")?
            .equals("x + S(y)", hyp)?
            .equals("S(x + y)", add_succ_r())?;
        let t2 = Theorem::as1().import_subst(&boxes, &["x + y"])?;
        let t3 = t2.box_mp(t1, &boxes)?;
        t3.box_chk("false", &boxes);
        let ti = t3.contradiction("S(y) = 0", &boxes)?;
        boxes.pop()?;

        ti.box_chk("x + S(y) = 0 -> S(y) = 0", &boxes);
        boxes.pop()?;
        boxes.pop()?;

        // Base case
        let _hyp0 = boxes.push_and_get("x + 0 = 0")?;
        let t0 = boxes.chain("0")?;
        boxes.pop()?;
        t0.box_chk("x + 0 = 0 -> 0 = 0", &boxes);

        ti.induction(t0, &boxes)
    })
}

pub fn neq_0_succ() -> Theorem {
    Theorem::as1()
}
