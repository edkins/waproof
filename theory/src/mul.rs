use crate::add::{
    add_0_r, add_assoc, add_comm, add_succ_l, add_succ_r, eq_add_0_r, neq_0_succ, succ_inj,
};
use crate::boxing::TheoremBox;
use crate::eq::TheoremEq;
use crate::util::{prove, Memo};
use kernel::pa_axiom::Theorem;

#[cfg(test)]
pub mod test {
    use super::*;

    #[test]
    fn test_mul() {
        mul_0_r().chk("@x(x * 0 = 0)");
        mul_succ_r().chk("@x(@y(x * S(y) = x * y + x))");
        mul_0_l().chk("@x(0 * x = 0)");
        mul_succ_l().chk("@x(@y(S(x) * y = x * y + y))");
        mul_comm().chk("@x(@y(x * y = y * x))");
        mul_add_distr_l().chk("@x(@y(@z((x + y) * z = x * z + y * z)))");
        mul_add_distr_r().chk("@x(@y(@z(x * (y + z) = x * y + x * z)))");
        mul_assoc().chk("@x(@y(@z(x * (y * z) = (x * y) * z)))");
        mult_is_1_r_succ().chk("@x(@y(S(x) * y = 1 -> y = 1))");
        mult_is_1_r().chk("@y(@x(x * y = 1 -> y = 1))");
    }
}

pub fn mul_0_r() -> Theorem {
    Theorem::am1()
}

pub fn mul_succ_r() -> Theorem {
    Theorem::am2()
}

pub fn mul_0_l() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove(&RESULT, |mut boxes| {
        boxes.push_var("x")?;
        let ih = boxes.push_and_get("0 * x = 0")?;

        // Inductive step
        let ti = boxes
            .chain("0 * S(x)")?
            .equals("0 * x + 0", mul_succ_r())?
            .equals("0 + 0", ih)?
            .equals("0", add_0_r())?;
        boxes.pop()?;
        boxes.pop()?;

        let t0 = boxes.chain("0 * 0")?.equals("0", mul_0_r())?;

        ti.induction(t0, &boxes)
    })
}

pub fn mul_succ_l() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove(&RESULT, |mut boxes| {
        boxes.push_var("x")?;
        boxes.push_var("y")?;
        let ih = boxes.push_and_get("S(x) * y = x * y + y")?;

        // Inductive step
        let ti = boxes
            .chain("S(x) * S(y)")?
            .equals("S(x) * y + S(x)", mul_succ_r())?
            .equals("(x * y + y) + S(x)", ih)?
            .equals("x * y + (y + S(x))", add_assoc())?
            .equals("x * y + (S(y + x))", add_succ_r())?
            .equals("x * y + (S(y) + x)", add_succ_l())?
            .equals("x * y + (x + S(y))", add_comm())?
            .equals("(x * y + x) + S(y)", add_assoc())?
            .equals("x * S(y) + S(y)", mul_succ_r())?;
        boxes.pop()?;
        boxes.pop()?;

        // Base case
        let t0 = boxes
            .chain("S(x) * 0")?
            .equals("0", mul_0_r())?
            .equals("0 + 0", add_0_r())?
            .equals("x * 0 + 0", mul_0_r())?;

        ti.induction(t0, &boxes)
    })
}

pub fn mul_comm() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove(&RESULT, |mut boxes| {
        boxes.push_var("x")?;
        boxes.push_var("y")?;
        let ih = boxes.push_and_get("x * y = y * x")?;

        let ti = boxes
            .chain("x * S(y)")?
            .equals("x * y + x", mul_succ_r())?
            .equals("y * x + x", ih)?
            .equals("S(y) * x", mul_succ_l())?;
        boxes.pop()?;
        boxes.pop()?;
        let t0 = boxes
            .chain("x * 0")?
            .equals("0", mul_0_r())?
            .equals("0 * x", mul_0_l())?;

        ti.induction(t0, &boxes)
    })
}

pub fn mul_add_distr_l() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove(&RESULT, |mut boxes| {
        boxes.push_var("x")?;
        boxes.push_var("y")?;
        boxes.push_var("z")?;
        let ih = boxes.push_and_get("(x + y) * z = x * z + y * z")?;

        let ti = boxes
            .chain("(x + y) * S(z)")?
            .equals("(x + y) * z + (x + y)", mul_succ_r())?
            .equals("(x * z + y * z) + (x + y)", ih)?
            .equals("(x * z + y * z) + (y + x)", add_comm())?
            .equals("x * z + (y * z + (y + x))", add_assoc())?
            .equals("x * z + ((y * z + y) + x)", add_assoc())?
            .equals("x * z + (x + (y * z + y))", add_comm())?
            .equals("(x * z + x) + (y * z + y)", add_assoc())?
            .equals("(x * S(z)) + (y * z + y)", mul_succ_r())?
            .equals("(x * S(z)) + (y * S(z))", mul_succ_r())?;
        boxes.pop()?;
        boxes.pop()?;
        let t0 = boxes
            .chain("(x + y) * 0")?
            .equals("0", mul_0_r())?
            .equals("0 + 0", add_0_r())?
            .equals("x * 0 + 0", mul_0_r())?
            .equals("x * 0 + y * 0", mul_0_r())?;

        ti.induction(t0, &boxes)
    })
}

pub fn mul_add_distr_r() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove(&RESULT, |mut boxes| {
        boxes.push_var("x")?;
        boxes.push_var("y")?;
        boxes.push_var("z")?;
        boxes
            .chain("x * (y + z)")?
            .equals("(y + z) * x", mul_comm())?
            .equals("y * x + z * x", mul_add_distr_l())?
            .equals("x * y + z * x", mul_comm())?
            .equals("x * y + x * z", mul_comm())
    })
}

pub fn mul_assoc() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove(&RESULT, |mut boxes| {
        boxes.push_var("x")?;
        boxes.push_var("y")?;
        boxes.push_var("z")?;
        let ih = boxes.push_and_get("x * (y * z) = (x * y) * z")?;

        let ti = boxes
            .chain("x * (y * S(z))")?
            .equals("x * (y * z + y)", mul_succ_r())?
            .equals("x * (y * z) + x * y", mul_add_distr_r())?
            .equals("(x * y) * z + x * y", ih)?
            .equals("(x * y) * S(z)", mul_succ_r())?;
        boxes.pop()?;
        boxes.pop()?;
        let t0 = boxes
            .chain("x * (y * 0)")?
            .equals("x * 0", mul_0_r())?
            .equals("0", mul_0_r())?
            .equals("(x * y) * 0", mul_0_r())?;

        ti.induction(t0, &boxes)
    })
}

fn mult_is_1_r_succ() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove(&RESULT, |mut boxes| {
        boxes.push_var("x")?;
        boxes.push_var("y")?;
        let _ih = boxes.push_and_get("S(x) * y = 1 -> y = 1")?;

        let hyp = boxes.push_and_get("S(x) * S(y) = 1")?;
        let t1 = boxes
            .chain("S(x * S(y) + y)")?
            .equals("x * S(y) + S(y)", add_succ_r())?
            .equals("S(x) * S(y)", mul_succ_l())?
            .equals("S(0)", hyp)?;
        let t2 = succ_inj().import_subst(&boxes, &["x * S(y) + y", "0"])?;
        t2.box_chk("S(x * S(y) + y) = S(0) -> x * S(y) + y = 0", &boxes);
        let t3 = t2.box_mp(t1, &boxes)?;
        t3.box_chk("x * S(y) + y = 0", &boxes);
        let t4 = eq_add_0_r().import_subst(&boxes, &["x * S(y)", "y"])?;
        let t5 = t4.box_mp(t3, &boxes)?;
        t5.box_chk("y = 0", &boxes);
        let ti = boxes.chain("S(y)")?.equals("S(0)", t5)?;
        boxes.pop()?;
        boxes.pop()?;
        boxes.pop()?;

        let hyp0 = boxes.push_and_get("S(x) * 0 = 1")?;
        let t0 = boxes
            .chain("0")?
            .equals("S(x) * 0", mul_0_r())?
            .equals("1", hyp0)?;
        boxes.pop()?;
        ti.induction(t0, &boxes)
    })
}

pub fn mult_is_1_r() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove(&RESULT, |mut boxes| {
        boxes.push_var("y")?;
        boxes.push_var("x")?;
        let _ih = boxes.push_and_get("x * y = 1 -> y = 1")?;
        let ti = mult_is_1_r_succ().import_subst(&boxes, &["x", "y"])?;
        boxes.pop()?;
        boxes.pop()?;

        let hyp = boxes.push_and_get("0 * y = 1")?;
        let t1 = boxes
            .chain("0")?
            .equals("0 * y", mul_0_l())?
            .equals("S(0)", hyp)?;
        let t0 = neq_0_succ()
            .import_subst(&boxes, &["0"])?
            .box_mp(t1, &boxes)?
            .contradiction("y = 1", &boxes)?;
        boxes.pop()?;

        ti.induction(t0, &boxes)
    })
}
