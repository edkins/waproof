use crate::wa_type::{BlockType, ValType};

// https://webassembly.github.io/spec/core/binary/values.html#binary-uint
fn uleb128(mut x: u64) -> Vec<u8> {
    let mut result = vec![];
    while x >= 128 {
        result.push(128 | (x & 127) as u8);
        x >>= 7;
    }
    result.push((x & 127) as u8);
    result
}

// https://webassembly.github.io/spec/core/binary/values.html#binary-sint
fn sleb128(mut x: i64) -> Vec<u8> {
    let mut result = vec![];
    while x >= 64 || x <= -65 {
        result.push(128 | (x & 127) as u8);
        x >>= 7;
    }
    result.push((x & 127) as u8);
    result
}

// https://webassembly.github.io/spec/core/binary/types.html#binary-valtype
fn valtype(t: &ValType) -> Vec<u8> {
    match t {
        ValType::I32 => vec![0x7f],
        ValType::I64 => vec![0x7e],
        ValType::F32 => vec![0x7d],
        ValType::F64 => vec![0x7c],
    }
}

// https://webassembly.github.io/spec/core/binary/instructions.html#binary-blocktype
fn blocktype(t: &BlockType) -> Vec<u8> {
    match t {
        BlockType::Empty => vec![0x40],
        BlockType::Val(t) => valtype(t),
        BlockType::Index(x) => sleb128(*x as i64),
    }
}

///////////////
// Instructions
///////////////

// https://webassembly.github.io/spec/core/binary/instructions.html#control-instructions
pub fn block_end(t: &BlockType, a: &[u8]) -> Vec<u8> {
    let mut result = vec![0x02];
    result.append(&mut blocktype(t));
    result.extend_from_slice(a);
    result.push(0x0b);
    result
}

// https://webassembly.github.io/spec/core/binary/instructions.html#variable-instructions
pub fn local_get(x: u32) -> Vec<u8> {
    let mut result = vec![0x20];
    result.append(&mut uleb128(x as u64));
    result.push((x & 127) as u8);
    result
}

// https://webassembly.github.io/spec/core/binary/instructions.html#numeric-instructions
pub fn i32_add() -> Vec<u8> {
    vec![0x6a]
}
