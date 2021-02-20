fn step_i32_add(c1: Specifier, c2: Specifier, c: Specifier) -> Formula {
    step(
        sequence(&[i32_const(c1), i32_const(c2), i32_add()]),
        sequence(&[i32_const(iadd32(c1, c2, c))])
    )
}
