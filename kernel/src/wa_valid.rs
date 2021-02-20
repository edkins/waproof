use crate::wa_binary;
use crate::wa_type::{func0, func2, BlockType, FuncType, LocalIdx, ValType};

#[derive(Debug)]
pub enum PreconditionNotMet {
    ContextMismatch,
    OutOfBounds(u32, u32),
    TypeCountMismatch(u32, u32),
    WrongValType(ValType, ValType),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Vec32<T>(pub Vec<T>);

impl<T> Vec32<T> {
    pub fn len(&self) -> u32 {
        self.0.len() as u32
    }
    pub fn get_ref(&self, i: u32) -> Result<&T, PreconditionNotMet> {
        if i < self.len() {
            Ok(&self.0[i as usize])
        } else {
            Err(PreconditionNotMet::OutOfBounds(i, self.len()))
        }
    }
}
impl<T: Copy> Vec32<T> {
    pub fn get(&self, i: u32) -> Result<T, PreconditionNotMet> {
        Ok(*self.get_ref(i)?)
    }
}
impl<T: Clone> Vec32<T> {
    pub fn prepend(&self, extra: &[T]) -> Self {
        let mut vec = extra.to_vec();
        vec.extend_from_slice(&self.0);
        Vec32(vec)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Context {
    types: Vec32<FuncType>,
    locals: Vec32<ValType>,
    labels: Vec32<ValType>,
}

// https://webassembly.github.io/spec/core/valid/conventions.html#formal-notation
pub struct TypeJudgement {
    c: Context,
    a: Vec<u8>,
    t: FuncType,
}

fn check_valtypes_equal(a: &[ValType], b: &[ValType]) -> Result<(), PreconditionNotMet> {
    if a.len() != b.len() {
        return Err(PreconditionNotMet::TypeCountMismatch(
            a.len() as u32,
            b.len() as u32,
        ));
    }
    for i in 0..a.len() {
        if a[i] != b[i] {
            return Err(PreconditionNotMet::WrongValType(a[i], b[i]));
        }
    }
    Ok(())
}

// Private functions
impl Context {
    fn check_local(&self, x: LocalIdx, t: ValType) -> Result<(), PreconditionNotMet> {
        if self.locals.get(x)? != t {
            return Err(PreconditionNotMet::WrongValType(t, self.locals.get(x)?));
        }
        Ok(())
    }

    // https://webassembly.github.io/spec/core/valid/types.html#valid-blocktype
    fn check_blocktype(
        &self,
        blocktype: &BlockType,
        t1: &[ValType],
        t2: &[ValType],
    ) -> Result<(), PreconditionNotMet> {
        match blocktype {
            BlockType::Empty => {
                check_valtypes_equal(t1, &[])?;
                check_valtypes_equal(t2, &[])?;
            }
            BlockType::Val(vt) => {
                check_valtypes_equal(t1, &[])?;
                check_valtypes_equal(t2, &[*vt])?;
            }
            BlockType::Index(x) => {
                check_valtypes_equal(t1, &self.types.get_ref(*x)?.params)?;
                check_valtypes_equal(t2, &self.types.get_ref(*x)?.result)?;
            }
        }
        Ok(())
    }

    fn with_labels_prepended(&self, extra_labels: &[ValType]) -> Self {
        Context {
            types: self.types.clone(),
            locals: self.locals.clone(),
            labels: self.labels.prepend(extra_labels),
        }
    }
}

impl Context {
    // https://webassembly.github.io/spec/core/valid/instructions.html#numeric-instructions
    pub fn i32_add(&self) -> TypeJudgement {
        TypeJudgement {
            c: self.clone(),
            a: wa_binary::i32_add(),
            t: func2(ValType::I32, ValType::I32, ValType::I32),
        }
    }

    // https://webassembly.github.io/spec/core/valid/instructions.html#variable-instructions
    pub fn local_get(&self, x: LocalIdx, t: ValType) -> Result<TypeJudgement, PreconditionNotMet> {
        self.check_local(x, t)?;
        Ok(TypeJudgement {
            c: self.clone(),
            a: wa_binary::local_get(x),
            t: func0(t),
        })
    }

    // https://webassembly.github.io/spec/core/valid/instructions.html#control-instructions
    pub fn block(
        &self,
        blocktype: BlockType,
        j: &TypeJudgement,
    ) -> Result<TypeJudgement, PreconditionNotMet> {
        let t1 = &j.t.params;
        let t2 = &j.t.result;
        self.check_blocktype(&blocktype, t1, t2)?;
        let c2 = self.with_labels_prepended(t2);
        if j.c != c2 {
            return Err(PreconditionNotMet::ContextMismatch);
        }
        Ok(TypeJudgement {
            c: self.clone(),
            a: wa_binary::block_end(&blocktype, &j.a),
            t: j.t.clone(),
        })
    }
}
