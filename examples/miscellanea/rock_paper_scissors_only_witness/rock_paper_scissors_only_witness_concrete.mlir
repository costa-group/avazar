module attributes {llzk.lang, llzk.main = !struct.type<@RockPaperScissors_0::@RockPaperScissors_0<[]>>} {
  poly.template @RockPaperScissors_0 {
    struct.def @RockPaperScissors_0 {
      struct.member @winner : !felt.type<"bn128"> {llzk.pub}
      function.def @compute(%arg0: !felt.type<"bn128">, %arg1: !felt.type<"bn128">) -> !struct.type<@RockPaperScissors_0::@RockPaperScissors_0<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@RockPaperScissors_0::@RockPaperScissors_0<[]>>
        %felt_const_2 = felt.const  2 : <"bn128">
        %0 = bool.cmp eq(%arg0, %felt_const_2) : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_3 = felt.const  3 : <"bn128">
        %1 = bool.cmp eq(%arg0, %felt_const_3) : !felt.type<"bn128">, !felt.type<"bn128">
        %2 = bool.or %0, %1 : i1, i1
        %felt_const_5 = felt.const  5 : <"bn128">
        %3 = bool.cmp eq(%arg0, %felt_const_5) : !felt.type<"bn128">, !felt.type<"bn128">
        %4 = bool.or %2, %3 : i1, i1
        bool.assert %4, "assertion failed"
        %felt_const_2_0 = felt.const  2 : <"bn128">
        %5 = bool.cmp eq(%arg1, %felt_const_2_0) : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_3_1 = felt.const  3 : <"bn128">
        %6 = bool.cmp eq(%arg1, %felt_const_3_1) : !felt.type<"bn128">, !felt.type<"bn128">
        %7 = bool.or %5, %6 : i1, i1
        %felt_const_5_2 = felt.const  5 : <"bn128">
        %8 = bool.cmp eq(%arg1, %felt_const_5_2) : !felt.type<"bn128">, !felt.type<"bn128">
        %9 = bool.or %7, %8 : i1, i1
        bool.assert %9, "assertion failed"
        %10 = bool.cmp eq(%arg0, %arg1) : !felt.type<"bn128">, !felt.type<"bn128">
        %11 = scf.if %10 -> (!felt.type<"bn128">) {
          %felt_const_0 = felt.const  0 : <"bn128">
          struct.writem %self[@winner] = %felt_const_0 : <@RockPaperScissors_0::@RockPaperScissors_0<[]>>, !felt.type<"bn128">
          scf.yield %felt_const_0 : !felt.type<"bn128">
        } else {
          %felt_const_2_3 = felt.const  2 : <"bn128">
          %12 = bool.cmp eq(%arg0, %felt_const_2_3) : !felt.type<"bn128">, !felt.type<"bn128">
          %felt_const_5_4 = felt.const  5 : <"bn128">
          %13 = bool.cmp eq(%arg1, %felt_const_5_4) : !felt.type<"bn128">, !felt.type<"bn128">
          %14 = bool.and %12, %13 : i1, i1
          %15 = scf.if %14 -> (!felt.type<"bn128">) {
            %felt_const_1 = felt.const  1 : <"bn128">
            struct.writem %self[@winner] = %felt_const_1 : <@RockPaperScissors_0::@RockPaperScissors_0<[]>>, !felt.type<"bn128">
            scf.yield %felt_const_1 : !felt.type<"bn128">
          } else {
            %felt_const_3_5 = felt.const  3 : <"bn128">
            %16 = bool.cmp eq(%arg0, %felt_const_3_5) : !felt.type<"bn128">, !felt.type<"bn128">
            %felt_const_2_6 = felt.const  2 : <"bn128">
            %17 = bool.cmp eq(%arg1, %felt_const_2_6) : !felt.type<"bn128">, !felt.type<"bn128">
            %18 = bool.and %16, %17 : i1, i1
            %19 = scf.if %18 -> (!felt.type<"bn128">) {
              %felt_const_1 = felt.const  1 : <"bn128">
              struct.writem %self[@winner] = %felt_const_1 : <@RockPaperScissors_0::@RockPaperScissors_0<[]>>, !felt.type<"bn128">
              scf.yield %felt_const_1 : !felt.type<"bn128">
            } else {
              %felt_const_5_7 = felt.const  5 : <"bn128">
              %20 = bool.cmp eq(%arg0, %felt_const_5_7) : !felt.type<"bn128">, !felt.type<"bn128">
              %felt_const_3_8 = felt.const  3 : <"bn128">
              %21 = bool.cmp eq(%arg1, %felt_const_3_8) : !felt.type<"bn128">, !felt.type<"bn128">
              %22 = bool.and %20, %21 : i1, i1
              %23 = scf.if %22 -> (!felt.type<"bn128">) {
                %felt_const_1 = felt.const  1 : <"bn128">
                struct.writem %self[@winner] = %felt_const_1 : <@RockPaperScissors_0::@RockPaperScissors_0<[]>>, !felt.type<"bn128">
                scf.yield %felt_const_1 : !felt.type<"bn128">
              } else {
                %felt_const_2_9 = felt.const  2 : <"bn128">
                struct.writem %self[@winner] = %felt_const_2_9 : <@RockPaperScissors_0::@RockPaperScissors_0<[]>>, !felt.type<"bn128">
                scf.yield %felt_const_2_9 : !felt.type<"bn128">
              }
              scf.yield %23 : !felt.type<"bn128">
            }
            scf.yield %19 : !felt.type<"bn128">
          }
          scf.yield %15 : !felt.type<"bn128">
        }
        function.return %self : !struct.type<@RockPaperScissors_0::@RockPaperScissors_0<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@RockPaperScissors_0::@RockPaperScissors_0<[]>>, %arg1: !felt.type<"bn128">, %arg2: !felt.type<"bn128">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@winner] : <@RockPaperScissors_0::@RockPaperScissors_0<[]>>, !felt.type<"bn128">
        %felt_const_2 = felt.const  2 : <"bn128">
        %1 = bool.cmp eq(%arg1, %felt_const_2) : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_3 = felt.const  3 : <"bn128">
        %2 = bool.cmp eq(%arg1, %felt_const_3) : !felt.type<"bn128">, !felt.type<"bn128">
        %3 = bool.or %1, %2 : i1, i1
        %felt_const_5 = felt.const  5 : <"bn128">
        %4 = bool.cmp eq(%arg1, %felt_const_5) : !felt.type<"bn128">, !felt.type<"bn128">
        %5 = bool.or %3, %4 : i1, i1
        bool.assert %5, "assertion failed"
        %felt_const_2_0 = felt.const  2 : <"bn128">
        %6 = bool.cmp eq(%arg2, %felt_const_2_0) : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_3_1 = felt.const  3 : <"bn128">
        %7 = bool.cmp eq(%arg2, %felt_const_3_1) : !felt.type<"bn128">, !felt.type<"bn128">
        %8 = bool.or %6, %7 : i1, i1
        %felt_const_5_2 = felt.const  5 : <"bn128">
        %9 = bool.cmp eq(%arg2, %felt_const_5_2) : !felt.type<"bn128">, !felt.type<"bn128">
        %10 = bool.or %8, %9 : i1, i1
        bool.assert %10, "assertion failed"
        %11 = bool.cmp eq(%arg1, %arg2) : !felt.type<"bn128">, !felt.type<"bn128">
        scf.if %11 {
        } else {
          %felt_const_2_3 = felt.const  2 : <"bn128">
          %12 = bool.cmp eq(%arg1, %felt_const_2_3) : !felt.type<"bn128">, !felt.type<"bn128">
          %felt_const_5_4 = felt.const  5 : <"bn128">
          %13 = bool.cmp eq(%arg2, %felt_const_5_4) : !felt.type<"bn128">, !felt.type<"bn128">
          %14 = bool.and %12, %13 : i1, i1
          scf.if %14 {
          } else {
            %felt_const_3_5 = felt.const  3 : <"bn128">
            %15 = bool.cmp eq(%arg1, %felt_const_3_5) : !felt.type<"bn128">, !felt.type<"bn128">
            %felt_const_2_6 = felt.const  2 : <"bn128">
            %16 = bool.cmp eq(%arg2, %felt_const_2_6) : !felt.type<"bn128">, !felt.type<"bn128">
            %17 = bool.and %15, %16 : i1, i1
            scf.if %17 {
            } else {
              %felt_const_5_7 = felt.const  5 : <"bn128">
              %18 = bool.cmp eq(%arg1, %felt_const_5_7) : !felt.type<"bn128">, !felt.type<"bn128">
              %felt_const_3_8 = felt.const  3 : <"bn128">
              %19 = bool.cmp eq(%arg2, %felt_const_3_8) : !felt.type<"bn128">, !felt.type<"bn128">
              %20 = bool.and %18, %19 : i1, i1
              scf.if %20 {
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
