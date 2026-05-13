module attributes {llzk.lang, llzk.main = !struct.type<@Juego_0::@Juego_0<[]>>} {
  poly.template @Juego_0 {
    struct.def @Juego_0 {
      struct.member @ganador : !felt.type<"bn128"> {llzk.pub}
      function.def @compute(%arg0: !felt.type<"bn128">, %arg1: !felt.type<"bn128">) -> !struct.type<@Juego_0::@Juego_0<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@Juego_0::@Juego_0<[]>>
        %0 = bool.cmp eq(%arg0, %arg1) : !felt.type<"bn128">, !felt.type<"bn128">
        %1 = scf.if %0 -> (!felt.type<"bn128">) {
          %felt_const_2 = felt.const  2 : <"bn128">
          struct.writem %self[@ganador] = %felt_const_2 : <@Juego_0::@Juego_0<[]>>, !felt.type<"bn128">
          scf.yield %felt_const_2 : !felt.type<"bn128">
        } else {
          %felt_const_0 = felt.const  0 : <"bn128">
          %2 = bool.cmp eq(%arg0, %felt_const_0) : !felt.type<"bn128">, !felt.type<"bn128">
          %felt_const_2 = felt.const  2 : <"bn128">
          %3 = bool.cmp eq(%arg1, %felt_const_2) : !felt.type<"bn128">, !felt.type<"bn128">
          %4 = bool.and %2, %3 : i1, i1
          %5 = scf.if %4 -> (!felt.type<"bn128">) {
            %felt_const_0_0 = felt.const  0 : <"bn128">
            struct.writem %self[@ganador] = %felt_const_0_0 : <@Juego_0::@Juego_0<[]>>, !felt.type<"bn128">
            scf.yield %felt_const_0_0 : !felt.type<"bn128">
          } else {
            %felt_const_1 = felt.const  1 : <"bn128">
            %6 = bool.cmp eq(%arg0, %felt_const_1) : !felt.type<"bn128">, !felt.type<"bn128">
            %felt_const_0_0 = felt.const  0 : <"bn128">
            %7 = bool.cmp eq(%arg1, %felt_const_0_0) : !felt.type<"bn128">, !felt.type<"bn128">
            %8 = bool.and %6, %7 : i1, i1
            %9 = scf.if %8 -> (!felt.type<"bn128">) {
              %felt_const_0_1 = felt.const  0 : <"bn128">
              struct.writem %self[@ganador] = %felt_const_0_1 : <@Juego_0::@Juego_0<[]>>, !felt.type<"bn128">
              scf.yield %felt_const_0_1 : !felt.type<"bn128">
            } else {
              %felt_const_2_1 = felt.const  2 : <"bn128">
              %10 = bool.cmp eq(%arg0, %felt_const_2_1) : !felt.type<"bn128">, !felt.type<"bn128">
              %felt_const_1_2 = felt.const  1 : <"bn128">
              %11 = bool.cmp eq(%arg1, %felt_const_1_2) : !felt.type<"bn128">, !felt.type<"bn128">
              %12 = bool.and %10, %11 : i1, i1
              %13 = scf.if %12 -> (!felt.type<"bn128">) {
                %felt_const_0_3 = felt.const  0 : <"bn128">
                struct.writem %self[@ganador] = %felt_const_0_3 : <@Juego_0::@Juego_0<[]>>, !felt.type<"bn128">
                scf.yield %felt_const_0_3 : !felt.type<"bn128">
              } else {
                %felt_const_1_3 = felt.const  1 : <"bn128">
                struct.writem %self[@ganador] = %felt_const_1_3 : <@Juego_0::@Juego_0<[]>>, !felt.type<"bn128">
                scf.yield %felt_const_1_3 : !felt.type<"bn128">
              }
              scf.yield %13 : !felt.type<"bn128">
            }
            scf.yield %9 : !felt.type<"bn128">
          }
          scf.yield %5 : !felt.type<"bn128">
        }
        function.return %self : !struct.type<@Juego_0::@Juego_0<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@Juego_0::@Juego_0<[]>>, %arg1: !felt.type<"bn128">, %arg2: !felt.type<"bn128">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@ganador] : <@Juego_0::@Juego_0<[]>>, !felt.type<"bn128">
        %1 = bool.cmp eq(%arg1, %arg2) : !felt.type<"bn128">, !felt.type<"bn128">
        scf.if %1 {
        } else {
          %felt_const_0 = felt.const  0 : <"bn128">
          %2 = bool.cmp eq(%arg1, %felt_const_0) : !felt.type<"bn128">, !felt.type<"bn128">
          %felt_const_2 = felt.const  2 : <"bn128">
          %3 = bool.cmp eq(%arg2, %felt_const_2) : !felt.type<"bn128">, !felt.type<"bn128">
          %4 = bool.and %2, %3 : i1, i1
          scf.if %4 {
          } else {
            %felt_const_1 = felt.const  1 : <"bn128">
            %5 = bool.cmp eq(%arg1, %felt_const_1) : !felt.type<"bn128">, !felt.type<"bn128">
            %felt_const_0_0 = felt.const  0 : <"bn128">
            %6 = bool.cmp eq(%arg2, %felt_const_0_0) : !felt.type<"bn128">, !felt.type<"bn128">
            %7 = bool.and %5, %6 : i1, i1
            scf.if %7 {
            } else {
              %felt_const_2_1 = felt.const  2 : <"bn128">
              %8 = bool.cmp eq(%arg1, %felt_const_2_1) : !felt.type<"bn128">, !felt.type<"bn128">
              %felt_const_1_2 = felt.const  1 : <"bn128">
              %9 = bool.cmp eq(%arg2, %felt_const_1_2) : !felt.type<"bn128">, !felt.type<"bn128">
              %10 = bool.and %8, %9 : i1, i1
              scf.if %10 {
              } else {
              }
            }
          }
        }
        function.return
      }
    }
  }
}
