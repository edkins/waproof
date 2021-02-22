use clap::clap_app;
use kernel::pa_axiom::{Theorem,TheoremError};
use kernel::pa_formula::{ExprVars,Formula,FormulaVars,SyntaxError};
use mersenne_twister::MT19937_64;
use rand::{Rng, Rand, SeedableRng};

fn rand_var<R:Rng>(r: &mut R) -> String {
    (r.gen_range(b'a',b'g') as char).to_string()
}

fn rand_expr<R:Rng>(r:&mut R) -> ExprVars {
    let x = f32::rand(r);
    if x < 0.2 {
        ExprVars::var(&rand_var(r))
    } else if x < 0.4 {
        ExprVars::z()
    } else if x < 0.8 {
        rand_expr(r).s()
    } else if x < 0.9 {
        rand_expr(r).add(rand_expr(r))
    } else {
        rand_expr(r).mul(rand_expr(r))
    }
}

fn rand_formula<R:Rng>(r:&mut R) -> Result<FormulaVars,SyntaxError> {
    let x = f32::rand(r);
    if x < 0.2 {
        Ok(FormulaVars::falsehood())
    } else if x < 0.4 {
        Ok(rand_expr(r).eq(rand_expr(r)))
    } else if x < 0.5 {
        rand_formula(r)?.imp(rand_formula(r)?)
    } else if x < 0.8 {
        rand_formula(r)?.forall(&rand_var(r))
    } else {
        Ok(rand_formula(r)?.memo())
    }
}

fn roughly<R:Rng>(vars: &[String], r: &mut R) -> Vec<String> {
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
    let mut result:Vec<String> = vec![];
    for vs in vss {
        for v in *vs {
            if !result.contains(v) {
                result.push(v.clone());
            }
        }
    }
    result
}

fn rand_axiom<R:Rng>(r:&mut R) -> Result<Theorem,TheoremError> {
    let x = f32::rand(r);
    if x < 0.10 {
        let a = rand_formula(r)?;
        let b = rand_formula(r)?;
        let vars = roughly(&merge_lists(&[a.free(), b.free()]),r);
        Theorem::a1(a, b, &vars)
    } else if x < 0.20 {
        let a = rand_formula(r)?;
        let b = rand_formula(r)?;
        let c = rand_formula(r)?;
        let vars = roughly(&merge_lists(&[a.free(), b.free(), c.free()]),r);
        Theorem::a2(a, b, c, &vars)
    } else if x < 0.30 {
        let a = rand_formula(r)?;
        let vars = roughly(&a.free(),r);
        Theorem::a3(a, &vars)
    } else if x < 0.40 {
        let a = rand_formula(r)?;
        let b = rand_formula(r)?;
        let x = rand_var(r);
        let vars:Vec<_> = merge_lists(&[a.free(), b.free()]).into_iter().filter(|y|*y != x).collect();
        let vars = roughly(&vars,r);
        Theorem::a4(a, b, &x, &vars)
    } else if x < 0.50 {
        let a = rand_formula(r)?;
        let x = rand_var(r);
        let vars = roughly(&a.free(),r);
        Theorem::a5(a, &x, &vars)
    } else if x < 0.60 {
        let a = rand_formula(r)?;
        let x = rand_var(r);
        let e = rand_expr(r);
        let vars:Vec<String> = a.free().iter().filter(|y|**y != x).map(|s|(**s).to_owned()).collect();
        let vars = roughly(&vars,r);
        Theorem::a6(a, &x, e, &vars)
    } else if x < 0.70 {
        let a = rand_formula(r)?;
        let x = rand_var(r);
        let vars:Vec<String> = a.free().iter().filter(|y|**y != x).map(|s|(**s).to_owned()).collect();
        let vars = roughly(&vars,r);
        Theorem::aind(a, &x, &vars)
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
        let a = rand_formula(r)?;
        let b = rand_formula(r)?;
        let vars = roughly(&merge_lists(&[a.free(), b.free()]),r);
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
    ).get_matches();

    let seed = matches.value_of("SEED").map(|s|s.parse::<u64>().unwrap()).unwrap_or(0x123456789abcdef);
    let mem_size = matches.value_of("MEMORY").map(|m|m.parse::<usize>().unwrap()).unwrap_or(1024);
    
    let mut mem:Vec<Option<Theorem>> = vec![None;mem_size];

    let mut i = 0;
    let mut rng: MT19937_64 = SeedableRng::from_seed(seed);

    loop {
        let a = mem[rng.gen_range(0, mem_size)].as_ref();
        let b = mem[rng.gen_range(0, mem_size)].as_ref();
        if let (Some(a),Some(b)) = (a,b) {
            if let Ok(t) = a.clone().mp(b.clone()) {
                if !t.formula().bound().is_empty() {
                    println!("MP!!!! {:?}", t);
                }
                validate(&t);
                mem[rng.gen_range(0, mem_size)] = Some(t);
            }
        }
        if let Ok(t) = rand_axiom(&mut rng) {
            i += 1;
            if i % 1000000 == 0 {
                println!("{:?}", t);
            }
            validate(&t);
            mem[rng.gen_range(0, mem_size)] = Some(t);
        }
    }
}
