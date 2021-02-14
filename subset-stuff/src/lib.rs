#[derive(Clone,Debug,Eq,PartialEq)]
pub enum PaType {
    Bool,
    Nat,
    Enum(Vec<PaVariant>),
}

#[derive(Clone,Debug,Eq,PartialEq)]
pub struct PaVariant(pub String, pub Vec<PaType>);

pub trait PaLift {
    fn pa_type() -> PaType;
}

impl PaLift for bool {
    fn pa_type() -> PaType {
        PaType::Bool
    }
}
