use crate::add::{add_0_r,add_comm,add_assoc,add_succ_r,add_succ_l};
use crate::boxing::TheoremBox;
use crate::eq::TheoremEq;
use crate::util::{prove, Memo};
use kernel::pa_axiom::Theorem;

/// ```
/// use theory::mul::mul_0_r;
///
/// mul_0_r().check("@x(x * 0 = 0)").unwrap();
/// ```
pub fn mul_0_r() -> Theorem {
    Theorem::am1()
}

/// ```
/// use theory::mul::mul_succ_r;
///
/// mul_succ_r().check("@x(@y(x * S(y) = x * y + x))").unwrap();
/// ```
pub fn mul_succ_r() -> Theorem {
    Theorem::am2()
}

/// ```
/// use theory::mul::mul_0_l;
///
/// mul_0_l().chk("@x(0 * x = 0)");
/// ```
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

/// ```
/// use theory::mul::mul_succ_l;
///
/// mul_succ_l().chk("@x(@y(S(x) * y = x * y + y))");
/// ```
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

/// ```
/// use theory::mul::mul_comm;
///
/// mul_comm().chk("@x(@y(x * y = y * x))");
/// ```
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

/// ```
/// use theory::mul::mul_add_distr_l;
///
/// mul_add_distr_l().chk("@x(@y(@z((x + y) * z = x * z + y * z)))");
/// ```
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
            .equals("(x + y) * z + (x + y)", mul_succ_r()).unwrap()
            .equals("(x * z + y * z) + (x + y)", ih).unwrap()
            .equals("(x * z + y * z) + (y + x)", add_comm()).unwrap()
            .equals("x * z + (y * z + (y + x))", add_assoc()).unwrap()
            .equals("x * z + ((y * z + y) + x)", add_assoc()).unwrap()
            .equals("x * z + (x + (y * z + y))", add_comm()).unwrap()
            .equals("(x * z + x) + (y * z + y)", add_assoc()).unwrap()
            .equals("(x * S(z)) + (y * z + y)", mul_succ_r()).unwrap()
            .equals("(x * S(z)) + (y * S(z))", mul_succ_r()).unwrap();
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

/// ```
/// use theory::mul::mul_add_distr_r;
///
/// mul_add_distr_r().chk("@x(@y(@z(x * (y + z) = x * y + x * z)))");
/// ```
pub fn mul_add_distr_r() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove(&RESULT, |mut boxes| {
        boxes.push_var("x")?;
        boxes.push_var("y")?;
        boxes.push_var("z")?;
        boxes.chain("x * (y + z)")?
            .equals("(y + z) * x", mul_comm())?
            .equals("y * x + z * x", mul_add_distr_l())?
            .equals("x * y + z * x", mul_comm())?
            .equals("x * y + x * z", mul_comm())
    })
}

/// ```
/// use theory::mul::mul_assoc;
///
/// mul_assoc().chk("@x(@y(@z(x * (y * z) = (x * y) * z)))");
/// ```
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
