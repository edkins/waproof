use crate::boxing::{self, Boxes, Boxing, TheoremBox};
use crate::util::TheoryError;
use kernel::pa_axiom::Theorem;
use kernel::pa_formula::{Expr, Formula};
use kernel::pa_parse::ToExpr;

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

impl Equalizer for Exact {
    fn prove_eq(
        &self,
        left: &Expr,
        right: &Expr,
        boxes: &[Boxing],
    ) -> Result<Theorem, TheoryError> {
        if let Formula::Eq(a, b) = boxing::peel_box_exact(self.0.formula(), boxes)?.formula() {
            if *left == **a && *right == **b {
                return Ok(self.0.clone());
            }
        }
        Err(TheoryError::StructuralMismatch)
    }
}

/// Adapt an equalizer to cover the case where it matches a single subexpression.
pub struct SiteAdapt<E: Equalizer>(E);

impl<E: Equalizer> SiteAdapt<E> {
    fn drill(&self, left: &Expr, right: &Expr, boxes: &[Boxing]) -> Result<Theorem, TheoryError> {
        match (left, right) {
            (Expr::S(a), Expr::S(b)) => {
                let ab = self.prove_eq(&**a, &**b, boxes)?;
                let t1 = Theorem::aes(); // @x(@y(x = y -> S(x) = S(y)))
                t1.import_subst(boxes, &[a, b])?.box_mp(ab, boxes)
            }
            (Expr::Add(a, c), Expr::Add(b, d)) => {
                if a == b {
                    let cd = self.prove_eq(&**c, &**d, boxes)?; // c = d
                    let t1 = Theorem::aea2(); // @x(@y(@z(y = z -> x + y = x + z)))
                    t1.import_subst(boxes, &[a, c, d])?.box_mp(cd, boxes)
                } else if c == d {
                    let ab = self.prove_eq(&**a, &**b, boxes)?; // a = b
                    let t1 = Theorem::aea1(); // @x(@y(@z(x = y -> x + z = y + z)))
                    t1.import_subst(boxes, &[a, b, c])?.box_mp(ab, boxes)
                } else {
                    Err(TheoryError::StructuralMismatch)
                }
            }
            (Expr::Mul(a, c), Expr::Mul(b, d)) => {
                if a == b {
                    let cd = self.prove_eq(&**c, &**d, boxes)?; // c = d
                    let t1 = Theorem::aem2(); // @x(@y(@z(y = z -> x * y = x * z)))
                    t1.import_subst(boxes, &[a, c, d])?.box_mp(cd, boxes)
                } else if c == d {
                    let ab = self.prove_eq(&**a, &**b, boxes)?; // a = b
                    let t1 = Theorem::aem1(); // @x(@y(@z(x = y -> x * z = y * z)))
                    t1.import_subst(boxes, &[a, b, c])?.box_mp(ab, boxes)
                } else {
                    Err(TheoryError::StructuralMismatch)
                }
            }
            (_, _) => Err(TheoryError::StructuralMismatch),
        }
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
        Exact(self.clone())
            .sym()
            .site()
            .prove_eq(left, right, boxes)
    }
}
