use crate::gen::TheoremGen;
use crate::hyp::TheoremHyp;
use kernel::pa_axiom::Theorem;
use kernel::pa_convenience::num;
use kernel::pa_formula::ExprVars;

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

fn x() -> ExprVars {
    ExprVars::var("x")
}

/// ```
/// use theory::add::add_0_l;
/// use theory::gen::TheoremGen;
///
/// add_0_l().check("@x(0 + x = x)").unwrap();
/// ```
pub fn add_0_l() -> Theorem {
    let t0 = add_0_r()
        .subst_gen(&[num(0)], &[])
        .unwrap()
        .check("0 + 0 = 0")
        .unwrap();
    let t1 = add_succ_r()
        .subst_gen(&[num(0), x()], &["x".to_owned()])
        .unwrap()
        .check("@x(0 + S(x) = S(0 + x))")
        .unwrap();
    let t2 = Theorem::ae3()
        .subst_gen(
            &[num(0).add(x().s()), num(0).add(x()).s(), x().s()],
            &["x".to_owned()],
        )
        .unwrap()
        .check("@x(0 + S(x) = S(0 + x) -> S(0 + x) = S(x) -> 0 + S(x) = S(x))")
        .unwrap();
    let t3 = t2
        .gen_mp(t1, 1)
        .unwrap()
        .check("@x(S(0 + x) = S(x) -> 0 + S(x) = S(x))")
        .unwrap();

    let t4 = Theorem::aes()
        .subst_gen(&[num(0).add(x()), x()], &["x".to_owned()])
        .unwrap()
        .check("@x(0 + x = x -> S(0 + x) = S(x))")
        .unwrap();

    let t5 = t4
        .compose(t3, 1)
        .unwrap()
        .check("@x(0 + x = x -> 0 + S(x) = S(x))")
        .unwrap();
    Theorem::aind(num(0).add(x()).eq(x()), "x", &[])
        .unwrap()
        .mp(t0)
        .unwrap()
        .mp(t5)
        .unwrap()
}
