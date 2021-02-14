use num_bigint::BigUint;

#[derive(Clone,Debug,Eq,PartialEq)]
pub enum PaType {
    Bool,
    Nat,
    Enum(Vec<PaVariant>),
}

#[derive(Clone,Debug,Eq,PartialEq)]
pub struct PaVariant(pub String, pub Vec<PaType>);

#[derive(Clone,Debug,Eq,PartialEq)]
pub enum PaValue {
    Bool(bool),
    Nat(BigUint),
    Variant(PaType, usize, Vec<PaValue>),
}

pub trait PaLift {
    fn pa_type() -> PaType;
    fn pa_lift(&self) -> PaValue;
}

impl PaLift for bool {
    fn pa_type() -> PaType {
        PaType::Bool
    }
    fn pa_lift(&self) -> PaValue {
        PaValue::Bool(*self)
    }
}

impl PaValue {
    pub fn typ(&self) -> PaType {
        match self {
            PaValue::Bool(_) => PaType::Bool,
            PaValue::Nat(_) => PaType::Nat,
            PaValue::Variant(t,_,_) => t.clone()
        }
    }
}
