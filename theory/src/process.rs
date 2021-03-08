use crate::boxing::{Boxes, TheoremBox};
use crate::eq::TheoremEq;
use crate::equalizer::MultiTheoremEqualizer;
use crate::script::{Script, ScriptEl};
use crate::util::TheoryError;
use kernel::pa_axiom::Theorem;

pub fn prove_script(script: &str, references: &[Theorem]) -> Result<Theorem, TheoryError> {
    let script: Script = script.parse()?;
    script.process(references)
}

struct TheoremSet {
    theorems: Vec<Theorem>,
    stacks: Vec<Boxes>,
}

impl TheoremSet {
    fn from_references(references: &[Theorem]) -> Self {
        TheoremSet {
            theorems: references.to_vec(),
            stacks: vec![Boxes::default(); references.len()],
        }
    }

    fn add(&mut self, theorem: &Theorem, stack: &Boxes) {
        self.theorems.push(theorem.clone());
        self.stacks.push(stack.clone());
    }

    fn equalizer(&self) -> MultiTheoremEqualizer {
        MultiTheoremEqualizer(self.theorems.clone())
    }
}

impl Script {
    fn process(&self, references: &[Theorem]) -> Result<Theorem, TheoryError> {
        let (t, boxes) = self.process_partial(references)?;
        if boxes.is_empty() {
            Ok(t)
        } else {
            Err(TheoryError::UnclosedBox)
        }
    }

    fn process_partial(&self, references: &[Theorem]) -> Result<(Theorem, Boxes), TheoryError> {
        let mut refs = TheoremSet::from_references(references);
        let mut boxes = Boxes::default();
        let mut current = None;
        for el in &self.0 {
            match el {
                ScriptEl::Pop => boxes.pop()?,
                ScriptEl::PushVar(x) => boxes.push_var(&x)?,
                ScriptEl::PushHyp(h) => {
                    let theorem = boxes.push_and_get(h)?;
                    refs.add(&theorem, &boxes);
                    current = Some(theorem);
                }
                ScriptEl::Chain(ch) => {
                    let mut theorem = boxes.chain(&ch[0])?;
                    let equalizer = refs.equalizer();
                    for rhs in &ch[1..] {
                        theorem = theorem.equals(rhs, equalizer.clone())?;
                    }
                    refs.add(&theorem, &boxes);
                    current = Some(theorem);
                }
                ScriptEl::Import(_) => {
                    panic!("Not yet handled: import");
                }
                ScriptEl::Induction => {
                    let t0 = current.clone().ok_or(TheoryError::NoTheorem)?;
                    let mut found = false;
                    for ti in &refs.theorems {
                        if let Ok(t) = ti.clone().induction(t0.clone(), &boxes) {
                            refs.add(&t, &boxes);
                            current = Some(t);
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        return Err(TheoryError::NoSuitableTheoremFound);
                    }
                }
            }
        }
        Ok((current.ok_or(TheoryError::NoTheorem)?, boxes))
    }
}
