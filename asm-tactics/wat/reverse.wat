(module
  (memory (import "js" "mem") 1)
  (func (export "reverse") (param i32) (param i32)
    (local i32)

    local.get 0
    local.get 1
    i32.add
    local.set 1
    
    loop
      local.get 1
      i32.const 1
      i32.sub
      local.tee 1

      local.get 0
      i32.le_u
      if
        return
      end

      local.get 0
      i32.load8_u
      local.set 2

      local.get 0
      local.get 1
      i32.load8_u
      i32.store8

      local.get 1
      local.get 2
      i32.store8

      local.get 0
      i32.const 1
      i32.add
      local.set 0

      br 0
    end
  )
)
