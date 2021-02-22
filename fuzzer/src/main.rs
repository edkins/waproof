use clap::clap_app;
use kernel::pa_axiom::{Theorem, TheoremError};
use kernel::pa_formula::{Expr, ExprVars, Formula, FormulaVars, SyntaxError};
use mersenne_twister::MT19937_64;
use rand::{Rand, Rng, SeedableRng};

fn rand_var<R: Rng>(r: &mut R) -> String {
    (r.gen_range(b'w', b'{') as char).to_string()
}

fn rand_expr<R: Rng>(r: &mut R, mem: &[Option<Theorem>]) -> ExprVars {
    let x = f32::rand(r);
    if x < 0.2 {
        ExprVars::var(&rand_var(r))
    } else if x < 0.4 {
        ExprVars::z()
    } else if x < 0.5 {
        rand_expr(r, mem).s()
    } else if x < 0.6 {
        rand_expr(r, mem).add(rand_expr(r, mem))
    } else if x < 0.7 {
        rand_expr(r, mem).mul(rand_expr(r, mem))
    } else {
        if let Some(t) = &mem[r.gen_range(0, mem.len())] {
            if let Some(e) = rand_fepiece(r, t.formula().formula()) {
                return e;
            }
        }
        rand_expr(r, mem)
    }
}

fn esize(e: &Expr) -> usize {
    match e {
        Expr::Var(_) => 1,
        Expr::Z => 1,
        Expr::S(e) => esize(e) + 1,
        Expr::Add(a, b) => esize(a) + esize(b) + 1,
        Expr::Mul(a, b) => esize(a) + esize(b) + 1,
    }
}

fn fsize(f: &Formula) -> usize {
    match f {
        Formula::False => 1,
        Formula::Eq(a, b) => esize(a) + esize(b) + 1,
        Formula::Imp(a, b) => fsize(a) + fsize(b) + 1,
        Formula::ForAll(_, a) => fsize(a) + 1,
        Formula::Memo(fv) => fsize(fv.formula()) + 1,
    }
}

fn rand_epiece<R: Rng>(r: &mut R, e: &Expr) -> ExprVars {
    if esize(e) < 20 && f32::rand(r) < 0.3 {
        e.reconstitute()
    } else {
        match e {
            Expr::Var(_) | Expr::Z => e.reconstitute(),
            Expr::S(a) => rand_epiece(r, a),
            Expr::Add(a, b) | Expr::Mul(a, b) => {
                if f32::rand(r) < 0.5 {
                    rand_epiece(r, a)
                } else {
                    rand_epiece(r, b)
                }
            }
        }
    }
}

fn rand_fepiece<R: Rng>(r: &mut R, f: &Formula) -> Option<ExprVars> {
    match f {
        Formula::False => None,
        Formula::Eq(a, b) => {
            if f32::rand(r) < 0.5 {
                Some(rand_epiece(r, a))
            } else {
                Some(rand_epiece(r, b))
            }
        }
        Formula::Imp(a, b) => {
            if f32::rand(r) < 0.5 {
                rand_fepiece(r, a)
            } else {
                rand_fepiece(r, b)
            }
        }
        Formula::ForAll(_, a) => rand_fepiece(r, a),
        Formula::Memo(fv) => rand_fepiece(r, fv.formula()),
    }
}

fn rand_piece<R: Rng>(r: &mut R, f: &Formula) -> Result<FormulaVars, SyntaxError> {
    if fsize(f) < 20 && f32::rand(r) < 0.3 {
        f.reconstitute()
    } else {
        match f {
            Formula::False => f.reconstitute(),
            Formula::Eq(_, _) => f.reconstitute(),
            Formula::Imp(a, b) => {
                if f32::rand(r) < 0.5 {
                    rand_piece(r, a)
                } else {
                    rand_piece(r, b)
                }
            }
            Formula::ForAll(_, a) => rand_piece(r, a),
            Formula::Memo(fv) => rand_piece(r, fv.formula()),
        }
    }
}

fn rand_formula<R: Rng>(r: &mut R, mem: &[Option<Theorem>]) -> Result<FormulaVars, SyntaxError> {
    let x = f32::rand(r);
    if x < 0.2 {
        Ok(FormulaVars::falsehood())
    } else if x < 0.4 {
        Ok(rand_expr(r, mem).eq(rand_expr(r, mem)))
    } else if x < 0.5 {
        rand_formula(r, mem)?.imp(rand_formula(r, mem)?)
    } else if x < 0.6 {
        rand_formula(r, mem)?.forall(&rand_var(r))
    } else if x < 0.7 {
        Ok(rand_formula(r, mem)?.memo())
    } else {
        if let Some(t) = &mem[r.gen_range(0, mem.len())] {
            rand_piece(r, t.formula().formula())
        } else {
            return rand_formula(r, mem);
        }
    }
}

fn roughly<R: Rng>(vars: &[String], r: &mut R) -> Vec<String> {
    let mut result = vec![];
    for v in vars {
        if f32::rand(r) < 0.95 {
            result.push(v.clone());
        }
        if f32::rand(r) < 0.05 {
            result.push(rand_var(r));
        }
    }
    result
}

fn merge_lists(vss: &[&[String]]) -> Vec<String> {
    let mut result: Vec<String> = vec![];
    for vs in vss {
        for v in *vs {
            if !result.contains(v) {
                result.push(v.clone());
            }
        }
    }
    result
}

fn rand_var_maybe_from<R: Rng>(r: &mut R, vars: &[String]) -> String {
    if vars.len() > 0 && f32::rand(r) < 0.8 {
        vars[r.gen_range(0, vars.len())].clone()
    } else {
        rand_var(r)
    }
}

fn rand_axiom<R: Rng>(
    r: &mut R,
    mem: &[Option<Theorem>],
    stats: &mut [usize],
) -> Result<Theorem, TheoremError> {
    let x = f32::rand(r);
    if x < 0.08 {
        let a = rand_formula(r, mem)?;
        let b = rand_formula(r, mem)?;
        let vars = roughly(&merge_lists(&[a.free(), b.free()]), r);
        let t = Theorem::a1(a, b, &vars)?;
        stats[0] += 1;
        Ok(t)
    } else if x < 0.16 {
        let a = rand_formula(r, mem)?;
        let b = rand_formula(r, mem)?;
        let c = rand_formula(r, mem)?;
        let vars = roughly(&merge_lists(&[a.free(), b.free(), c.free()]), r);
        let t = Theorem::a2(a, b, c, &vars)?;
        stats[1] += 1;
        Ok(t)
    } else if x < 0.24 {
        let a = rand_formula(r, mem)?;
        let vars = roughly(&a.free(), r);
        let t = Theorem::a3(a, &vars)?;
        stats[2] += 1;
        Ok(t)
    } else if x < 0.32 {
        let a = rand_formula(r, mem)?;
        let b = rand_formula(r, mem)?;
        let vars = merge_lists(&[a.free(), b.free()]);
        let x = rand_var_maybe_from(r, &vars);
        let vars: Vec<_> = vars.into_iter().filter(|y| *y != x).collect();
        let vars = roughly(&vars, r);
        let t = Theorem::a4(a, b, &x, &vars)?;
        stats[3] += 1;
        Ok(t)
    } else if x < 0.40 {
        let a = rand_formula(r, mem)?;
        let x = rand_var(r);
        let vars = roughly(&a.free(), r);
        let t = Theorem::a5(a, &x, &vars)?;
        stats[4] += 1;
        Ok(t)
    } else if x < 0.48 {
        let a = rand_formula(r, mem)?;
        let x = rand_var_maybe_from(r, a.free());
        let e = rand_expr(r, mem);
        let vars: Vec<String> = a
            .free()
            .iter()
            .filter(|y| **y != x)
            .map(|s| (**s).to_owned())
            .collect();
        let vars = roughly(&merge_lists(&[&vars, e.free()]), r);
        let t = Theorem::a6(a, &x, e, &vars)?;
        stats[5] += 1;
        Ok(t)
    } else if x < 0.56 {
        let a = rand_formula(r, mem)?;
        let x = rand_var(r);
        let vars: Vec<String> = a
            .free()
            .iter()
            .filter(|y| **y != x)
            .map(|s| (**s).to_owned())
            .collect();
        let vars = roughly(&vars, r);
        let t = Theorem::aind(a, &x, &vars)?;
        stats[6] += 1;
        Ok(t)
    } else if x < 0.63 {
        let a = rand_formula(r, mem)?;
        let vars = roughly(&a.free(), r);
        let t = Theorem::memo(a, &vars)?;
        stats[7] += 1;
        Ok(t)
    } else if x < 0.70 {
        let a = rand_formula(r, mem)?;
        let vars = roughly(&a.free(), r);
        let t = Theorem::unmemo(a, &vars)?;
        stats[8] += 1;
        Ok(t)
    } else if x < 0.72 {
        Ok(Theorem::ae1())
    } else if x < 0.74 {
        Ok(Theorem::ae2())
    } else if x < 0.76 {
        Ok(Theorem::ae3())
    } else if x < 0.78 {
        Ok(Theorem::aes())
    } else if x < 0.80 {
        Ok(Theorem::aea1())
    } else if x < 0.82 {
        Ok(Theorem::aea2())
    } else if x < 0.84 {
        Ok(Theorem::aem1())
    } else if x < 0.86 {
        Ok(Theorem::aem2())
    } else if x < 0.88 {
        Ok(Theorem::as1())
    } else if x < 0.90 {
        Ok(Theorem::as2())
    } else if x < 0.92 {
        Ok(Theorem::aa1())
    } else if x < 0.94 {
        Ok(Theorem::aa2())
    } else if x < 0.92 {
        Ok(Theorem::am1())
    } else if x < 0.94 {
        Ok(Theorem::am2())
    } else {
        let a = rand_formula(r, mem)?;
        let b = rand_formula(r, mem)?;
        let vars = roughly(&merge_lists(&[a.free(), b.free()]), r);
        Theorem::a1(a, b, &vars)
    }
}

fn validate(t: &Theorem) {
    if *t.formula().formula() == Formula::False {
        panic!("False formula!");
    }
    if !t.formula().free().is_empty() {
        panic!("Formula has free vars!");
    }
}

fn main() {
    let matches = clap_app!(fuzzer =>
        (about: "Tries random combinations of axioms until it proves false")
        (@arg SEED: -s +takes_value "Random seed to use")
        (@arg MEMORY: -m +takes_value "Number of memory slots")
    )
    .get_matches();

    let seed = matches
        .value_of("SEED")
        .map(|s| s.parse::<u64>().unwrap())
        .unwrap_or(0x123456789abcdef);
    let mem_size = matches
        .value_of("MEMORY")
        .map(|m| m.parse::<usize>().unwrap())
        .unwrap_or(16);

    let mut mem: Vec<Option<Theorem>> = vec![None; mem_size];

    let mut i = 0;
    let mut rng: MT19937_64 = SeedableRng::from_seed(seed);
    let mut stats = [0; 9];

    loop {
        let a = mem[rng.gen_range(0, mem_size)].as_ref();
        let b = mem[rng.gen_range(0, mem_size)].as_ref();
        if let (Some(a), Some(b)) = (a, b) {
            if let Ok(t) = a.clone().mp(b.clone()) {
                i += 1;
                if i % 1000 == 0 {
                    println!("{:?}", t.formula().formula());
                    println!("{:?}", stats);
                }
                validate(&t);
                mem[rng.gen_range(0, mem_size)] = Some(t);
            }
        }
        if let Ok(t) = rand_axiom(&mut rng, &mem, &mut stats) {
            validate(&t);
            mem[rng.gen_range(0, mem_size)] = Some(t);
        }
    }
}
