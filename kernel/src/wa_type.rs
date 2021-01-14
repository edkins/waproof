// https://webassembly.github.io/spec/core/syntax/modules.html#syntax-typeidx
pub type LocalIdx = u32;
pub type TypeIdx = u32;

/*#[derive(Clone,Debug,Eq,PartialEq)]
pub enum Type {
    Val(ValType),
    Func(FuncType),
}*/

// https://webassembly.github.io/spec/core/syntax/types.html#syntax-valtype
#[derive(Clone,Copy,Debug,Eq,PartialEq)]
pub enum ValType {
    I32,
    I64,
    F32,
    F64,
}

// https://webassembly.github.io/spec/core/syntax/instructions.html#syntax-blocktype
#[derive(Clone,Debug,Eq,PartialEq)]
pub enum BlockType {
    Empty,
    Val(ValType),
    Index(TypeIdx),
}

// https://webassembly.github.io/spec/core/syntax/types.html#function-types
#[derive(Clone,Debug,Eq,PartialEq)]
pub struct FuncType {
    pub params: Vec<ValType>,
    pub result: Vec<ValType>,
}

// Convenience functions

pub fn func0(r:ValType) -> FuncType {
    FuncType{
        params: vec![],
        result: vec![r],
    }
}

pub fn func2(a:ValType, b:ValType, r:ValType) -> FuncType {
    FuncType{
        params: vec![a,b],
        result: vec![r],
    }
}
