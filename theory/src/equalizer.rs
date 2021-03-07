use crate::boxing::{self, Boxes, Boxing, TheoremBox};
use crate::util::TheoryError;
use kernel::pa_axiom::Theorem;
use kernel::pa_formula::{Expr, Formula};
use kernel::pa_parse::ToExpr;
use std::collections::HashMap;

pub trait Equalizer: Sized {
    fn prove_eq(&self, left: &Expr, right: &Expr, boxes: &[Boxing])
        -> Result<Theorem, TheoryError>;
    fn sym(self) -> SymAdapt<Self> {
        SymAdapt(self)
    }
    fn site(self) -> SiteAdapt<Self> {
        SiteAdapt(self)
    }
}

/// Adapt an equalizer to cover reflexive and symmetric cases
/// i.e. where the two expressions are identical or equality is reversed
/// from what the equalizer is expecting.
pub struct SymAdapt<E: Equalizer>(E);

impl<E: Equalizer> Equalizer for SymAdapt<E> {
    fn prove_eq(
        &self,
        left: &Expr,
        right: &Expr,
        boxes: &[Boxing],
    ) -> Result<Theorem, TheoryError> {
        if left == right {
            Theorem::ae1().import_subst(boxes, &[left])
        } else {
            self.0.prove_eq(left, right, boxes).or_else(|_| {
                let t0 = self.0.prove_eq(right, left, boxes)?;
                let t1 = Theorem::ae2().import_subst(boxes, &[right, left])?;
                t1.box_mp(t0, boxes)
            })
        }
    }
}

/// Return equal iff the given theorem says so. No cleverness, requires
/// the right number of boxes and no substitutions.
pub struct Exact(pub Theorem);

pub fn expect_eq(a: &Formula) -> Result<(&Expr, &Expr), TheoryError> {
    a.cases(
        || Err(TheoryError::StructuralMismatch),
        |b, c| Ok((b, c)),
        |_, _| Err(TheoryError::StructuralMismatch),
        |_, _| Err(TheoryError::StructuralMismatch),
    )
}

impl Equalizer for Exact {
    fn prove_eq(
        &self,
        left: &Expr,
        right: &Expr,
        boxes: &[Boxing],
    ) -> Result<Theorem, TheoryError> {
        let ab = boxing::peel_box_exact(self.0.formula(), boxes)?;
        let (a, b) = expect_eq(&ab)?;
        if left == a && right == b {
            return Ok(self.0.clone());
        } else {
            Err(TheoryError::StructuralMismatch)
        }
    }
}

/// Adapt an equalizer to cover the case where it matches a single subexpression.
pub struct SiteAdapt<E: Equalizer>(E);

impl<E: Equalizer> SiteAdapt<E> {
    fn drill(&self, left: &Expr, right: &Expr, boxes: &[Boxing]) -> Result<Theorem, TheoryError> {
        left.cases(
            |_| Err(TheoryError::StructuralMismatch),
            || Err(TheoryError::StructuralMismatch),
            |a| {
                let b = expect_s(right)?;
                let ab = self.prove_eq(a, b, boxes)?;
                let t1 = Theorem::aes(); // @x(@y(x = y -> S(x) = S(y)))
                t1.import_subst(boxes, &[a, b])?.box_mp(ab, boxes)
            },
            |a, c| {
                let (b, d) = expect_add(right)?;
                if a == b {
                    let cd = self.prove_eq(c, d, boxes)?; // c = d
                    let t1 = Theorem::aea2(); // @x(@y(@z(y = z -> x + y = x + z)))
                    t1.import_subst(boxes, &[a, c, d])?.box_mp(cd, boxes)
                } else if c == d {
                    let ab = self.prove_eq(a, b, boxes)?; // a = b
                    let t1 = Theorem::aea1(); // @x(@y(@z(x = y -> x + z = y + z)))
                    t1.import_subst(boxes, &[a, b, c])?.box_mp(ab, boxes)
                } else {
                    Err(TheoryError::StructuralMismatch)
                }
            },
            |a, c| {
                let (b, d) = expect_mul(right)?;
                if a == b {
                    let cd = self.prove_eq(c, d, boxes)?; // c = d
                    let t1 = Theorem::aem2(); // @x(@y(@z(y = z -> x * y = x * z)))
                    t1.import_subst(boxes, &[a, c, d])?.box_mp(cd, boxes)
                } else if c == d {
                    let ab = self.prove_eq(a, b, boxes)?; // a = b
                    let t1 = Theorem::aem1(); // @x(@y(@z(x = y -> x * z = y * z)))
                    t1.import_subst(boxes, &[a, b, c])?.box_mp(ab, boxes)
                } else {
                    Err(TheoryError::StructuralMismatch)
                }
            },
        )
    }
}

impl<E: Equalizer> Equalizer for SiteAdapt<E> {
    fn prove_eq(
        &self,
        left: &Expr,
        right: &Expr,
        boxes: &[Boxing],
    ) -> Result<Theorem, TheoryError> {
        if left == right {
            Theorem::ae1().import_subst(boxes, &[left])
        } else {
            self.drill(left, right, boxes)
                .or_else(|_| self.0.prove_eq(left, right, boxes))
        }
    }
}

pub fn expect_z(e: &Expr) -> Result<(), TheoryError> {
    e.cases(
        |_| Err(TheoryError::StructuralMismatch),
        || Ok(()),
        |_| Err(TheoryError::StructuralMismatch),
        |_, _| Err(TheoryError::StructuralMismatch),
        |_, _| Err(TheoryError::StructuralMismatch),
    )
}

pub fn expect_s(e: &Expr) -> Result<&Expr, TheoryError> {
    e.cases(
        |_| Err(TheoryError::StructuralMismatch),
        || Err(TheoryError::StructuralMismatch),
        |y| Ok(y),
        |_, _| Err(TheoryError::StructuralMismatch),
        |_, _| Err(TheoryError::StructuralMismatch),
    )
}

pub fn expect_add(e: &Expr) -> Result<(&Expr, &Expr), TheoryError> {
    e.cases(
        |_| Err(TheoryError::StructuralMismatch),
        || Err(TheoryError::StructuralMismatch),
        |_| Err(TheoryError::StructuralMismatch),
        |c, d| Ok((c, d)),
        |_, _| Err(TheoryError::StructuralMismatch),
    )
}

pub fn expect_mul(e: &Expr) -> Result<(&Expr, &Expr), TheoryError> {
    e.cases(
        |_| Err(TheoryError::StructuralMismatch),
        || Err(TheoryError::StructuralMismatch),
        |_| Err(TheoryError::StructuralMismatch),
        |_, _| Err(TheoryError::StructuralMismatch),
        |c, d| Ok((c, d)),
    )
}

pub enum ExprRef<'a> {
    Var(&'a str),
    Z,
    S(&'a Expr),
    Add(&'a Expr, &'a Expr),
    Mul(&'a Expr, &'a Expr),
}

pub fn as_enum<'a>(e: &'a Expr) -> ExprRef<'a> {
    e.cases(
        |x| ExprRef::Var(x),
        || ExprRef::Z,
        ExprRef::S,
        ExprRef::Add,
        ExprRef::Mul,
    )
}

fn figure_out_substitutions(
    map: &mut HashMap<String, Expr>,
    before: &Expr,
    after: &Expr,
) -> Result<(), TheoryError> {
    match as_enum(before) {
        ExprRef::Var(x) => {
            if let Some(y) = map.get(x) {
                if y == after {
                    Ok(())
                } else {
                    Err(TheoryError::StructuralMismatch)
                }
            } else {
                map.insert(x.to_owned(), after.clone());
                Ok(())
            }
        }
        ExprRef::Z => expect_z(after),
        ExprRef::S(x) => {
            let y = expect_s(after)?;
            figure_out_substitutions(map, x, y)
        }
        ExprRef::Add(a, b) => {
            let (c, d) = expect_add(after)?;
            figure_out_substitutions(map, a, c)?;
            figure_out_substitutions(map, b, d)
        }
        ExprRef::Mul(a, b) => {
            let (c, d) = expect_mul(after)?;
            figure_out_substitutions(map, a, c)?;
            figure_out_substitutions(map, b, d)
        }
    }
}

/// An equalizer which imports a particular theorem into the box context and
/// provides appropriate substitutions for all of its variables.
pub struct ImportSubst(pub Theorem);

/// All of boxes must be vars, else panic.
fn substitution_map_to_list(map: &HashMap<String, Expr>, boxes: &[Boxing]) -> Vec<Expr> {
    boxes
        .iter()
        .map(|b| {
            if let Boxing::Var(x) = b {
                map.get(x).cloned().unwrap_or(Expr::z())
            } else {
                panic!("Box is not a var");
            }
        })
        .collect()
}

impl ImportSubst {
    fn prove_eq_import_subst(
        &self,
        left: &Expr,
        right: &Expr,
        boxes: &[Boxing],
    ) -> Result<Theorem, TheoryError> {
        let (my_boxes, my_left, my_right) = boxing::peel_box_until_eq(self.0.formula())?;
        if my_boxes.iter().all(Boxing::is_var) {
            // We currently only handle substitution in the case where
            // all the boxes are variables.
            let mut map = HashMap::default();
            figure_out_substitutions(&mut map, &my_left, left)?;
            figure_out_substitutions(&mut map, &my_right, right)?;
            let values = substitution_map_to_list(&map, &my_boxes);
            self.0.clone().import_subst(boxes, &values)
        } else {
            Err(TheoryError::StructuralMismatch)
        }
    }
}

impl Equalizer for ImportSubst {
    fn prove_eq(
        &self,
        left: &Expr,
        right: &Expr,
        boxes: &[Boxing],
    ) -> Result<Theorem, TheoryError> {
        self.prove_eq_import_subst(left, right, boxes).or_else(|_| {
            // Fall back to no substitution, no import if all the boxes are correct (same behaviour
            // as Exact)
            Exact(self.0.clone()).prove_eq(left, right, boxes)
        })
    }
}

impl Boxes {
    pub fn chain(&self, expr: impl ToExpr + Clone) -> Result<Theorem, TheoryError> {
        Theorem::ae1().import_subst(self, &[expr])
    }
}

impl Equalizer for Theorem {
    fn prove_eq(
        &self,
        left: &Expr,
        right: &Expr,
        boxes: &[Boxing],
    ) -> Result<Theorem, TheoryError> {
        ImportSubst(self.clone())
            .sym()
            .site()
            .prove_eq(left, right, boxes)
    }
}

#[cfg(test)]
mod test {
    use crate::boxing::Boxes;
    use crate::eq::TheoremEq;
    use kernel::pa_axiom::Theorem;

    #[test]
    fn import_subst_0_plus_0() {
        let t0 = Boxes::default()
            .chain("0 + 0")
            .unwrap()
            .equals("0", Theorem::aa1())
            .unwrap();
        t0.chk("0 + 0 = 0");
    }
}
