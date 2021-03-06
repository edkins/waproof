use crate::util::TheoryError;
use kernel::pa_axiom::Theorem;
use kernel::pa_formula::{Expr, Formula};

pub trait TheoremGen: Sized {
    fn absent_gen(self, gen: &[String]) -> Result<Self, TheoryError>;
    fn gen_mp(self, other: Self, count: usize) -> Result<Self, TheoryError>;
    fn outer_rename(self, x: &str, y: &str) -> Result<Self, TheoryError>;
    fn reorder_gen(self, xs: &[String]) -> Result<Self, TheoryError>;
    fn subst_gen(self, es: &[Expr], gen: &[String]) -> Result<Self, TheoryError>;
    fn subst_one(self, x: &str, e: Expr) -> Result<Self, TheoryError>;
}

pub fn expect_false(a: &Formula) -> Result<(), TheoryError> {
    a.cases(
        || Ok(()),
        |_, _| Err(TheoryError::NotFalse),
        |_, _| Err(TheoryError::NotFalse),
        |_, _| Err(TheoryError::NotFalse),
    )
}

pub fn expect_imp(a: &Formula) -> Result<(&Formula, &Formula), TheoryError> {
    a.cases(
        || Err(TheoryError::NotImp),
        |_, _| Err(TheoryError::NotImp),
        |b, c| Ok((b, c)),
        |_, _| Err(TheoryError::NotImp),
    )
}

pub fn expect_forall(a: &Formula) -> Result<(&'_ str, &'_ Formula), TheoryError> {
    a.cases(
        || Err(TheoryError::NotForAll),
        |_, _| Err(TheoryError::NotForAll),
        |_, _| Err(TheoryError::NotForAll),
        |x, b| Ok((x, b)),
    )
}

pub fn peel_forall(a: &Formula) -> Result<(String, Formula), TheoryError> {
    let (x, f) = expect_forall(a)?;
    Ok((x.to_owned(), (*f).clone()))
}

pub fn peel_all_outer_foralls(a: &Formula) -> (Vec<String>, Formula) {
    let mut vars = vec![];
    let mut f = a.clone();
    loop {
        if let Ok((x, f2)) = expect_forall(&f) {
            vars.push(x.to_owned());
            f = (*f2).clone();
        } else {
            return (vars, f);
        }
    }
}

pub fn peel_foralls(a: &Formula, count: usize) -> Result<(Vec<String>, Formula), TheoryError> {
    let mut vars = vec![];
    let mut f = a.clone();
    for _ in 0..count {
        let (x, f2) = expect_forall(&f)?;
        vars.push(x.to_owned());
        f = (*f2).clone();
    }
    Ok((vars, f))
}

fn peel_foralls_until(a: &Formula, x: &str) -> Result<(Vec<String>, Formula), TheoryError> {
    let mut vars = vec![];
    let mut f = a.clone();
    loop {
        let (y, f2) = expect_forall(&f).map_err(|_| TheoryError::NotOuterVar(x.to_owned()))?;
        if y == x {
            break;
        } else {
            vars.push(y.to_owned());
            f = (*f2).clone();
        }
    }
    Ok((vars, f))
}

pub fn check_expr_environment(e: &Expr, vars: &[String]) -> Result<(), TheoryError> {
    for x in e.free().slice() {
        if !vars.contains(x) {
            return Err(TheoryError::SubstNotInEnvironment(x.clone()));
        }
    }
    Ok(())
}

// This implementation is so silly
fn incr(x: &str) -> String {
    let mut carry = true;
    let mut result = String::new();
    for ch in x.chars().rev() {
        if carry {
            if ch == '9' {
                result.push('0');
            } else if ch.is_ascii_digit() {
                result.push(((ch as u8) + 1) as char);
                carry = false;
            } else {
                result.push('1');
                result.push(ch);
                carry = false;
            }
        } else {
            result.push(ch);
        }
    }
    if carry {
        result.push('1');
    }
    result.chars().rev().collect()
}

pub fn rename_to_avoid(xs: &[String], avoid_lists: &[&[String]]) -> Vec<String> {
    let mut result = vec![];
    for x in xs {
        if avoid_lists.iter().any(|list| list.contains(x)) {
            let mut y = incr(x);
            while xs.contains(&y) || avoid_lists.iter().any(|list| list.contains(&y)) {
                y = incr(&y);
            }
            result.push(y);
        } else {
            result.push(x.clone());
        }
    }
    result
}

impl TheoremGen for Theorem {
    fn outer_rename(self, x: &str, y: &str) -> Result<Self, TheoryError> {
        if x == y {
            return Ok(self);
        }

        let (mut vars, xf) = peel_foralls_until(self.formula(), x)?;
        let (_, f) = peel_forall(&xf)?;

        if vars.iter().any(|y| y == x) {
            return Err(TheoryError::RenameOuterConflict(x.to_owned()));
        }
        if f.has_bound(x) {
            return Err(TheoryError::RenameInnerConflict(x.to_owned()));
        }

        // self: @v...@x(f[x])
        let t1 = Theorem::a5(xf, y, &vars)?.gen_mp(self, vars.len())?; // @v...@y(@x(f[x]))

        vars.push(y.to_owned());
        let t2 = Theorem::a6(f, x, Expr::var(y), &vars)?;
        Ok(t2.gen_mp(t1, vars.len())?) // @v...@y(f[y])
    }

    fn subst_one(self, x: &str, e: Expr) -> Result<Self, TheoryError> {
        let (vars, xf) = peel_foralls_until(self.formula(), x)?;
        let (_, f) = peel_forall(&xf)?;

        check_expr_environment(&e, &vars)?;

        if vars.iter().any(|y| y == x) {
            return Err(TheoryError::SubstOuterConflict(x.to_owned()));
        }

        // self: @v...@x(f[x])
        let t1 = Theorem::a6(f, x, e, &vars)?; // @v...(@x(f[x]) -> f[e])
        Ok(t1.gen_mp(self, vars.len())?)
    }

    fn absent_gen(mut self, gen: &[String]) -> Result<Self, TheoryError> {
        let bounds = self.formula().bound().slice().to_vec();
        for x in gen.iter().rev() {
            if bounds.contains(x) {
                return Err(TheoryError::NotAbsentGen(x.clone()));
            }
            self = Theorem::a5(self.formula().clone(), x, &[])?.mp(self)?;
        }
        Ok(self)
    }

    fn subst_gen(mut self, es: &[Expr], gen: &[String]) -> Result<Self, TheoryError> {
        for expr in es {
            check_expr_environment(&expr, gen)?;
        }

        let (orig_vars, f) = peel_foralls(self.formula(), es.len())?;

        for y in f.bound().slice() {
            if gen.contains(y) {
                return Err(TheoryError::SubstInnerConflict(y.clone()));
            }
        }

        // @o...(f[o...])
        let vars = rename_to_avoid(&orig_vars, &[&f.bound().slice(), &gen]);
        for i in 0..vars.len() {
            self = self.outer_rename(&orig_vars[i], &vars[i])?;
        }
        // @v...(f[v...])
        self = self.absent_gen(gen)?;
        // @g...@v...(f[v...])
        for i in 0..vars.len() {
            self = self.subst_one(&vars[i], es[i].clone())?;
        }
        // @g...f[e...]
        Ok(self)
    }

    fn gen_mp(self, other: Self, count: usize) -> Result<Self, TheoryError> {
        if count == 0 {
            Ok(self.mp(other)?)
        } else {
            let (xs, xa) = peel_foralls(self.formula(), count - 1)?;
            let (ys, yb) = peel_foralls(other.formula(), count - 1)?;
            for i in 0..count - 1 {
                if xs[i] != ys[i] {
                    return Err(TheoryError::VarMismatch(xs[i].clone(), ys[i].clone()));
                }
            }
            let (x, ab) = peel_forall(&xa)?;
            let (y, a) = peel_forall(&yb)?;
            if x != y {
                return Err(TheoryError::VarMismatch(x, y));
            }
            let (hyp, b) = expect_imp(&ab)?;
            if *hyp != a {
                return Err(TheoryError::WrongHyp);
            }
            // self: @xs...@x(a->b)
            // other: @xs...@x(a)
            let t0 = Theorem::a4(a, b.clone(), &x, &xs)?; // @xs...(@x(a->b)->(@x(a)->@x(b)))
            let t1 = t0.gen_mp(self, count - 1)?;
            let t2 = t1.gen_mp(other, count - 1)?;
            Ok(t2)
        }
    }

    fn reorder_gen(self, xs: &[String]) -> Result<Self, TheoryError> {
        let (vars, _) = peel_foralls(self.formula(), xs.len())?;
        for x in xs {
            if !vars.contains(x) {
                return Err(TheoryError::NotReorder(x.clone()));
            }
        }
        for x in &vars {
            if !xs.contains(x) {
                return Err(TheoryError::NotReorder(x.clone()));
            }
        }

        let exprs: Vec<_> = vars.iter().map(|x| Expr::var(x)).collect();
        self.subst_gen(&exprs, xs)
    }
}

#[cfg(test)]
mod test {
    use super::{incr, TheoremGen};
    use kernel::pa_axiom::Theorem;
    use kernel::pa_convenience::num;
    use kernel::pa_formula::{Expr, Formula};

    #[test]
    fn outer_rename_same() {
        let t = Theorem::aa2(); // @x(@y(x + S(y) = S(x + y)))
        let t1 = t.outer_rename("x", "x").unwrap();
        let e: Formula = "@x(@y(x + S(y) = S(x + y)))".parse().unwrap();
        assert_eq!(e, *t1.formula());
    }

    #[test]
    fn outer_rename_1() {
        let t = Theorem::aa2(); // @x(@y(x + S(y) = S(x + y)))
        let t1 = t.outer_rename("x", "x1").unwrap();
        let e: Formula = "@x1(@y(x1 + S(y) = S(x1 + y)))".parse().unwrap();
        assert_eq!(e, *t1.formula());
    }

    #[test]
    fn outer_rename_2() {
        let t = Theorem::aa2(); // @x(@y(x + S(y) = S(x + y)))
        let t1 = t.outer_rename("y", "y1").unwrap();
        let e: Formula = "@x(@y1(x + S(y1) = S(x + y1)))".parse().unwrap();
        assert_eq!(e, *t1.formula());
    }

    #[test]
    fn outer_rename_3() {
        let t = Theorem::aea1(); // @x(@y(@z(x = y -> x + z = y + z)))
        let t1 = t.outer_rename("z", "w").unwrap();
        let e: Formula = "@x(@y(@w(x = y -> x + w = y + w)))".parse().unwrap();
        assert_eq!(e, *t1.formula());
    }

    #[test]
    fn outer_rename_outer_conflict() {
        let t = Theorem::aea1(); // @x(@y(@z(x = y -> x + z = y + z)))
        assert!(t.outer_rename("y", "x").is_err());
    }

    #[test]
    fn outer_rename_outer_inner() {
        let t = Theorem::aea1(); // @x(@y(@z(x = y -> x + z = y + z)))
        assert!(t.outer_rename("y", "z").is_err());
    }

    #[test]
    fn absent_gen_none() {
        let t = Theorem::aa1().check("@x(x + 0 = x)").unwrap();
        let t1 = t.absent_gen(&[]).unwrap();
        t1.check("@x(x + 0 = x)").unwrap();
    }

    fn v(xs: &[&str]) -> Vec<String> {
        xs.iter().map(|x| (*x).to_owned()).collect()
    }

    #[test]
    fn absent_gen_one() {
        let t = Theorem::aa1().check("@x(x + 0 = x)").unwrap();
        let t1 = t.absent_gen(&v(&["y"])).unwrap();
        t1.check("@y(@x(x + 0 = x))").unwrap();
    }

    #[test]
    fn absent_gen_three() {
        let t = Theorem::aa1().check("@x(x + 0 = x)").unwrap();
        let t1 = t.absent_gen(&v(&["w", "z", "y"])).unwrap();
        t1.check("@w(@z(@y(@x(x + 0 = x))))").unwrap();
    }

    #[test]
    fn absent_gen_same_fail() {
        let t = Theorem::aa1().check("@x(x + 0 = x)").unwrap();
        assert!(t.absent_gen(&v(&["x"])).is_err());
    }

    #[test]
    fn subst_one_const() {
        let t = Theorem::aa1().check("@x(x + 0 = x)").unwrap();
        let t1 = t.subst_one("x", num(0)).unwrap();
        t1.check("0 + 0 = 0").unwrap();
    }

    #[test]
    fn subst_one_var1_err() {
        let t = Theorem::aa2().check("@x(@y(x + S(y) = S(x + y)))").unwrap();
        assert!(t.subst_one("x", "S(y)".parse().unwrap()).is_err());
    }

    #[test]
    fn subst_one_varz_err() {
        let t = Theorem::aa2().check("@x(@y(x + S(y) = S(x + y)))").unwrap();
        assert!(t.subst_one("x", "S(z)".parse().unwrap()).is_err());
    }

    #[test]
    fn subst_one_var2() {
        let t = Theorem::aa2().check("@x(@y(x + S(y) = S(x + y)))").unwrap();
        let t1 = t.subst_one("y", "S(x)".parse().unwrap()).unwrap();
        t1.check("@x(x + S(S(x)) = S(x + S(x)))").unwrap();
    }

    #[test]
    fn incr_x() {
        assert_eq!(&incr("x"), "x1");
    }

    #[test]
    fn incr_x1() {
        assert_eq!(&incr("x1"), "x2");
    }

    #[test]
    fn incr_x9() {
        assert_eq!(&incr("x9"), "x10");
    }

    #[test]
    fn incr_x89() {
        assert_eq!(&incr("x89"), "x90");
    }

    #[test]
    fn incr_x94() {
        assert_eq!(&incr("x94"), "x95");
    }

    #[test]
    fn incr_x99() {
        assert_eq!(&incr("x99"), "x100");
    }

    #[test]
    fn subst_gen_x_x() {
        let t = Theorem::aa1().check("@x(x + 0 = x)").unwrap();
        let t1 = t.subst_gen(&[Expr::var("x")], &v(&["x"])).unwrap();
        t1.check("@x(x + 0 = x)").unwrap();
    }

    #[test]
    fn subst_gen_x_y() {
        let t = Theorem::aa1().check("@x(x + 0 = x)").unwrap();
        let t1 = t.subst_gen(&[Expr::var("y")], &v(&["y"])).unwrap();
        t1.check("@y(y + 0 = y)").unwrap();
    }

    #[test]
    fn subst_gen_x_0() {
        let t = Theorem::aa1().check("@x(x + 0 = x)").unwrap();
        let t1 = t.subst_gen(&[num(0)], &v(&[])).unwrap();
        t1.check("0 + 0 = 0").unwrap();
    }

    #[test]
    fn subst_gen_x_0_gen() {
        let t = Theorem::aa1().check("@x(x + 0 = x)").unwrap();
        let t1 = t.subst_gen(&[num(0)], &v(&["z"])).unwrap();
        t1.check("@z(0 + 0 = 0)").unwrap();
    }

    #[test]
    fn subst_gen_x_0_genx() {
        let t = Theorem::aa1().check("@x(x + 0 = x)").unwrap();
        let t1 = t.subst_gen(&[num(0)], &v(&["x"])).unwrap();
        t1.check("@x(0 + 0 = 0)").unwrap();
    }

    #[test]
    fn subst_gen_x_yz() {
        let t = Theorem::aa1().check("@x(x + 0 = x)").unwrap();
        let t1 = t
            .subst_gen(&[Expr::var("y") + Expr::var("z")], &v(&["z", "y"]))
            .unwrap();
        t1.check("@z(@y((y+z) + 0 = (y+z)))").unwrap();
    }

    #[test]
    fn subst_gen_xy_01() {
        let t = Theorem::aa2().check("@x(@y(x + S(y) = S(x + y)))").unwrap();
        let t1 = t.subst_gen(&[num(0), num(1)], &[]).unwrap();
        t1.check("0 + S(1) = S(0 + 1)").unwrap();
    }

    #[test]
    fn subst_gen_xy_yx1() {
        let t = Theorem::aa2().check("@x(@y(x + S(y) = S(x + y)))").unwrap();
        let t1 = t
            .subst_gen(&[Expr::var("y"), Expr::var("x")], &v(&["x", "y"]))
            .unwrap();
        t1.check("@x(@y(y + S(x) = S(y + x)))").unwrap();
    }

    #[test]
    fn subst_gen_xy_yx2() {
        let t = Theorem::aa2().check("@x(@y(x + S(y) = S(x + y)))").unwrap();
        let t1 = t
            .subst_gen(&[Expr::var("y"), Expr::var("x")], &v(&["y", "x"]))
            .unwrap();
        t1.check("@y(@x(y + S(x) = S(y + x)))").unwrap();
    }

    #[test]
    fn subst_gen_xy_xx() {
        let t = Theorem::aa2().check("@x(@y(x + S(y) = S(x + y)))").unwrap();
        let t1 = t
            .subst_gen(&[Expr::var("x"), Expr::var("x")], &v(&["x"]))
            .unwrap();
        t1.check("@x(x + S(x) = S(x + x))").unwrap();
    }

    #[test]
    fn gen_mp_one() {
        let t = Theorem::aa1().check("@x(x + 0 = x)").unwrap();
        let t1 = Theorem::aea1()
            .check("@x(@y(@z(x = y -> x + z = y + z)))")
            .unwrap();
        let t2 = t1
            .subst_gen(
                &[Expr::var("x") + num(0), Expr::var("x"), num(0)],
                &v(&["x"]),
            )
            .unwrap();
        t2.checkr("@x(x + 0 = x -> (x + 0) + 0 = x + 0)").unwrap();
        let t3 = t2.gen_mp(t, 1).unwrap();
        t3.checkr("@x((x + 0) + 0 = x + 0)").unwrap();
    }

    #[test]
    fn gen_mp_two() {
        let t = Theorem::aa1()
            .absent_gen(&v(&["z"]))
            .unwrap()
            .reorder_gen(&v(&["x", "z"]))
            .unwrap()
            .check("@x(@z(x + 0 = x))")
            .unwrap();
        let t1 = Theorem::aea1()
            .check("@x(@y(@z(x = y -> x + z = y + z)))")
            .unwrap();
        let t2 = t1
            .subst_gen(&[Expr::var("x") + num(0), Expr::var("x")], &v(&["x"]))
            .unwrap()
            .check("@x(@z(x + 0 = x -> (x + 0) + z = x + z))")
            .unwrap();
        let t3 = t2.gen_mp(t, 2).unwrap();
        t3.checkr("@x(@z((x + 0) + z = x + z))").unwrap();
    }

    #[test]
    fn reorder_gen_same() {
        let t1 = Theorem::aea1()
            .check("@x(@y(@z(x = y -> x + z = y + z)))")
            .unwrap();
        let t2 = t1.reorder_gen(&v(&["x", "y", "z"])).unwrap();
        t2.checkr("@x(@y(@z(x = y -> x + z = y + z)))").unwrap();
    }

    #[test]
    fn reorder_gen_different() {
        let t1 = Theorem::aea1()
            .check("@x(@y(@z(x = y -> x + z = y + z)))")
            .unwrap();
        let t2 = t1.reorder_gen(&v(&["y", "z", "x"])).unwrap();
        t2.checkr("@y(@z(@x(x = y -> x + z = y + z)))").unwrap();
    }
}
