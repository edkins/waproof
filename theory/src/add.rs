use crate::util::{prove_with_script, Memo};
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
    prove_with_script(
        &RESULT,
        "
var x {
    var y {
        hyp S(x) + y = S(x + y)
        {
            chain S(x) + S(y)
                = S(S(x) + y)
                = S(S(x + y))
                = S(x + S(y));
        }
    }
    chain S(x) + 0
        = S(x)
        = S(x + 0);
    induction;
}",
        &[add_succ_r(), add_0_r()],
    )
}

pub fn add_comm() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove_with_script(
        &RESULT,
        "
var x {
    var y {
        hyp x + y = y + x {
            chain x + S(y)
                = S(x + y)
                = S(y + x)
                = S(y) + x;
        }
    }
    chain x + 0 = x = 0 + x;
    induction;
}",
        &[add_succ_r(), add_succ_l(), add_0_r(), add_0_l()],
    )
}

pub fn add_assoc() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove_with_script(
        &RESULT,
        "
var x {
    var y {
        var z {
            hyp x + (y + z) = (x + y) + z
            {
                chain x + (y + S(z))
                    = x + S(y + z)
                    = S(x + (y + z))
                    = S((x + y) + z)
                    = (x + y) + S(z);
            }
        }
        chain x + (y + 0)
            = x + y
            = (x + y) + 0;
        induction;
    }
}",
        &[add_succ_r(), add_0_r()],
    )
}

pub fn succ_inj() -> Theorem {
    Theorem::as2()
}

pub fn add_cancel_r() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove_with_script(
        &RESULT,
        "
var x {
    var y {
        var z {
            hyp x + z = y + z -> x = y
            {
                hyp x + S(z) = y + S(z)
                {
                    chain S(x + z)
                        = x + S(z)
                        = y + S(z)
                        = S(y + z);
                    import S(x + z) = S(y + z) -> x + z = y + z;
                    mp x + z = y + z;
                    mp x = y;
                }
            }
        }
        hyp x + 0 = y + 0
        {
            chain x = x + 0 = y + 0 = y;
        }
        induction;
    }
}",
        &[succ_inj(), add_succ_r(), add_0_r()],
    )
}

pub fn add_cancel_l() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove_with_script(
        &RESULT,
        "
var x {
    var y {
        var z {
            hyp x + y = x + z
            {
                chain y + x
                    = x + y
                    = x + z
                    = z + x;
                import y + x = z + x -> y = z;
                mp y = z;
            }
        }
    }
}",
        &[add_comm(), add_cancel_r()],
    )
}

pub fn neq_0_succ() -> Theorem {
    Theorem::as1()
}

pub fn eq_add_0_r() -> Theorem {
    thread_local! {
        static RESULT: Memo = Memo::default();
    }
    prove_with_script(
        &RESULT,
        "
var x {
    var y {
        hyp x + y = 0 -> y = 0
        {
            hyp x + S(y) = 0
            {
                chain 0
                    = x + S(y)
                    = S(x + y);
                import !(0 = S(x + y));
                mp false;
                exfalso S(y) = 0;
            }
        }
    }
    hyp x + 0 = 0
    {
        chain 0;
    }
    induction;
}",
        &[add_succ_r(), neq_0_succ()],
    )
    /*prove(&RESULT, |mut boxes| {
        boxes.push_var("x")?;
        boxes.push_var("y")?;
        let _ih = boxes.push_and_get("x + y = 0 -> y = 0")?;

        let hyp = boxes.push_and_get("x + S(y) = 0")?;
        let t1 = boxes
            .chain("0")?
            .equals("x + S(y)", hyp)?
            .equals("S(x + y)", add_succ_r())?;
        let t2 = neq_0_succ().import_as(&boxes, "!(0 = S(x + y))")?;
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
    })*/
}
