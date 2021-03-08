use crate::boxing::{self, Boxes, TheoremBox};
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
    depths: Vec<usize>,
    depth: usize,
}

impl TheoremSet {
    fn from_references(references: &[Theorem]) -> Self {
        TheoremSet {
            theorems: references.to_vec(),
            depths: vec![0; references.len()],
            depth: 0,
        }
    }

    fn add(&mut self, theorem: &Theorem) {
        self.theorems.push(theorem.clone());
        self.depths.push(self.depth);
    }

    fn incr_depth(&mut self) {
        self.depth += 1;
    }

    fn decr_depth(&mut self) {
        self.depth -= 1;
        for i in 0..self.depths.len() {
            self.depths[i] = self.depths[i].min(self.depth);
        }
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
                ScriptEl::Pop => {
                    boxes.pop()?;
                    refs.decr_depth();
                }
                ScriptEl::PushVar(x) => {
                    boxes.push_var(&x)?;
                    refs.incr_depth();
                }
                ScriptEl::PushHyp(h) => {
                    let theorem = boxes.push_and_get(h)?;
                    refs.incr_depth();
                    refs.add(&theorem);
                    current = Some(theorem);
                }
                ScriptEl::Chain(ch) => {
                    let mut theorem = boxes.chain(&ch[0])?;
                    let equalizer = refs.equalizer();
                    for rhs in &ch[1..] {
                        theorem = theorem.equals(rhs, equalizer.clone())?;
                    }
                    refs.add(&theorem);
                    current = Some(theorem);
                }
                ScriptEl::Import(formula) => {
                    let mut found = false;
                    for candidate in &refs.theorems {
                        if let Ok(t) = candidate.clone().import_as(&boxes, formula) {
                            refs.add(&t);
                            current = Some(t);
                            found = true;
                            break;
                        }
                    }
                    if !found {
                        return Err(TheoryError::NoSuitableTheoremFound);
                    }
                }
                ScriptEl::ModusPonens(formula) => {
                    let current_theorem = current.clone().ok_or(TheoryError::NoTheorem)?;
                    let mut found = false;
                    for i in 0..refs.theorems.len() {
                        let candidate = &refs.theorems[i];
                        let depth = refs.depths[i];
                        if let Ok(imported) = candidate.clone().import(depth, &boxes) {
                            if let Ok(t) = current_theorem.clone().box_mp(imported.clone(), &boxes)
                            {
                                if boxing::peel_box_exact(t.formula(), &boxes)? == *formula {
                                    refs.add(&t);
                                    current = Some(t);
                                    found = true;
                                    break;
                                }
                            } else if let Ok(t) = imported.box_mp(current_theorem.clone(), &boxes) {
                                if boxing::peel_box_exact(t.formula(), &boxes)? == *formula {
                                    refs.add(&t);
                                    current = Some(t);
                                    found = true;
                                    break;
                                }
                            }
                        }
                    }
                    if !found {
                        return Err(TheoryError::NoSuitableTheoremFound);
                    }
                }
                ScriptEl::ExFalso(formula) => {
                    let current_theorem = current.clone().ok_or(TheoryError::NoTheorem)?;
                    let t = current_theorem.contradiction(formula, &boxes)?;
                    refs.add(&t);
                    current = Some(t);
                }
                ScriptEl::Induction => {
                    let t0 = current.clone().ok_or(TheoryError::NoTheorem)?;
                    let mut found = false;
                    for ti in &refs.theorems {
                        if let Ok(t) = ti.clone().induction(t0.clone(), &boxes) {
                            refs.add(&t);
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
