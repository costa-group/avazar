module attributes {llzk.lang, llzk.main = !struct.type<@LessThan_0::@LessThan_0<[]>>} {
  poly.template @LessThan_0 {
    struct.def @LessThan_0 {
      struct.member @out : !felt.type<"bn128"> {llzk.pub}
      struct.member @n2b_in : !felt.type<"bn128">
      struct.member @n2b_out : !array.type<11 x !felt.type<"bn128">>
      function.def @compute(%arg0: !array.type<2 x !felt.type<"bn128">>) -> !struct.type<@LessThan_0::@LessThan_0<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@LessThan_0::@LessThan_0<[]>>
        %nondet = llzk.nondet : !array.type<11 x !felt.type<"bn128">>
        %felt_const_10 = felt.const  10 : <"bn128">
        %felt_const_1 = felt.const  1 : <"bn128">
        %felt_const_0 = felt.const  0 : <"bn128">
        %0 = bool.cmp ne(%felt_const_1, %felt_const_0) : !felt.type<"bn128">, !felt.type<"bn128">
        bool.assert %0, "assertion failed"
        %felt_const_0_0 = felt.const  0 : <"bn128">
        %1 = cast.toindex %felt_const_0_0 : !felt.type<"bn128">
        %2 = array.read %arg0[%1] : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        %felt_const_1024 = felt.const  1024 : <"bn128">
        %3 = felt.add %2, %felt_const_1024 : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_1_1 = felt.const  1 : <"bn128">
        %4 = cast.toindex %felt_const_1_1 : !felt.type<"bn128">
        %5 = array.read %arg0[%4] : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        %6 = felt.sub %3, %5 : !felt.type<"bn128">, !felt.type<"bn128">
        struct.writem %self[@n2b_in] = %6 : <@LessThan_0::@LessThan_0<[]>>, !felt.type<"bn128">
        %felt_const_0_2 = felt.const  0 : <"bn128">
        %felt_const_1_3 = felt.const  1 : <"bn128">
        %felt_const_0_4 = felt.const  0 : <"bn128">
        %7:3 = scf.while (%arg1 = %felt_const_1_3, %arg2 = %felt_const_0_4, %arg3 = %felt_const_0_2) : (!felt.type<"bn128">, !felt.type<"bn128">, !felt.type<"bn128">) -> (!felt.type<"bn128">, !felt.type<"bn128">, !felt.type<"bn128">) {
          %felt_const_11 = felt.const  11 : <"bn128">
          %11 = bool.cmp lt(%arg2, %felt_const_11) : !felt.type<"bn128">, !felt.type<"bn128">
          scf.condition(%11) %arg1, %arg2, %arg3 : !felt.type<"bn128">, !felt.type<"bn128">, !felt.type<"bn128">
        } do {
        ^bb0(%arg1: !felt.type<"bn128">, %arg2: !felt.type<"bn128">, %arg3: !felt.type<"bn128">):
          %11 = felt.shr %6, %arg2 : !felt.type<"bn128">, !felt.type<"bn128">
          %felt_const_1_7 = felt.const  1 : <"bn128">
          %12 = felt.bit_and %11, %felt_const_1_7 : !felt.type<"bn128">, !felt.type<"bn128">
          %13 = cast.toindex %arg2 : !felt.type<"bn128">
          array.write %nondet[%13] = %12 : <11 x !felt.type<"bn128">>, !felt.type<"bn128">
          %14 = cast.toindex %arg2 : !felt.type<"bn128">
          %15 = array.read %nondet[%14] : <11 x !felt.type<"bn128">>, !felt.type<"bn128">
          %16 = felt.mul %15, %felt_const_1_3 : !felt.type<"bn128">, !felt.type<"bn128">
          %17 = felt.add %arg3, %16 : !felt.type<"bn128">, !felt.type<"bn128">
          %18 = felt.add %arg1, %arg1 : !felt.type<"bn128">, !felt.type<"bn128">
          %felt_const_1_8 = felt.const  1 : <"bn128">
          %19 = felt.add %arg2, %felt_const_1_8 : !felt.type<"bn128">, !felt.type<"bn128">
          scf.yield %18, %19, %17 : !felt.type<"bn128">, !felt.type<"bn128">, !felt.type<"bn128">
        }
        %felt_const_1_5 = felt.const  1 : <"bn128">
        %felt_const_10_6 = felt.const  10 : <"bn128">
        %8 = cast.toindex %felt_const_10_6 : !felt.type<"bn128">
        %9 = array.read %nondet[%8] : <11 x !felt.type<"bn128">>, !felt.type<"bn128">
        %10 = felt.sub %felt_const_1_5, %9 : !felt.type<"bn128">, !felt.type<"bn128">
        struct.writem %self[@out] = %10 : <@LessThan_0::@LessThan_0<[]>>, !felt.type<"bn128">
        struct.writem %self[@n2b_out] = %nondet : <@LessThan_0::@LessThan_0<[]>>, !array.type<11 x !felt.type<"bn128">>
        function.return %self : !struct.type<@LessThan_0::@LessThan_0<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@LessThan_0::@LessThan_0<[]>>, %arg1: !array.type<2 x !felt.type<"bn128">>) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@out] : <@LessThan_0::@LessThan_0<[]>>, !felt.type<"bn128">
        %1 = struct.readm %arg0[@n2b_in] : <@LessThan_0::@LessThan_0<[]>>, !felt.type<"bn128">
        %2 = struct.readm %arg0[@n2b_out] : <@LessThan_0::@LessThan_0<[]>>, !array.type<11 x !felt.type<"bn128">>
        %felt_const_10 = felt.const  10 : <"bn128">
        %felt_const_1 = felt.const  1 : <"bn128">
        %felt_const_0 = felt.const  0 : <"bn128">
        %3 = bool.cmp ne(%felt_const_1, %felt_const_0) : !felt.type<"bn128">, !felt.type<"bn128">
        bool.assert %3, "assertion failed"
        %felt_const_0_0 = felt.const  0 : <"bn128">
        %4 = cast.toindex %felt_const_0_0 : !felt.type<"bn128">
        %5 = array.read %arg1[%4] : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        %felt_const_1024 = felt.const  1024 : <"bn128">
        %6 = felt.add %5, %felt_const_1024 : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_1_1 = felt.const  1 : <"bn128">
        %7 = cast.toindex %felt_const_1_1 : !felt.type<"bn128">
        %8 = array.read %arg1[%7] : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        %9 = felt.sub %6, %8 : !felt.type<"bn128">, !felt.type<"bn128">
        constrain.eq %1, %9 : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_0_2 = felt.const  0 : <"bn128">
        %felt_const_1_3 = felt.const  1 : <"bn128">
        %felt_const_0_4 = felt.const  0 : <"bn128">
        %10:3 = scf.while (%arg2 = %felt_const_0_2, %arg3 = %felt_const_1_3, %arg4 = %felt_const_0_4) : (!felt.type<"bn128">, !felt.type<"bn128">, !felt.type<"bn128">) -> (!felt.type<"bn128">, !felt.type<"bn128">, !felt.type<"bn128">) {
          %felt_const_11 = felt.const  11 : <"bn128">
          %14 = bool.cmp lt(%arg4, %felt_const_11) : !felt.type<"bn128">, !felt.type<"bn128">
          scf.condition(%14) %arg2, %arg3, %arg4 : !felt.type<"bn128">, !felt.type<"bn128">, !felt.type<"bn128">
        } do {
        ^bb0(%arg2: !felt.type<"bn128">, %arg3: !felt.type<"bn128">, %arg4: !felt.type<"bn128">):
          %14 = cast.toindex %arg4 : !felt.type<"bn128">
          %15 = array.read %2[%14] : <11 x !felt.type<"bn128">>, !felt.type<"bn128">
          %16 = cast.toindex %arg4 : !felt.type<"bn128">
          %17 = array.read %2[%16] : <11 x !felt.type<"bn128">>, !felt.type<"bn128">
          %felt_const_1_7 = felt.const  1 : <"bn128">
          %18 = felt.sub %17, %felt_const_1_7 : !felt.type<"bn128">, !felt.type<"bn128">
          %19 = felt.mul %15, %18 : !felt.type<"bn128">, !felt.type<"bn128">
          %felt_const_0_8 = felt.const  0 : <"bn128">
          constrain.eq %19, %felt_const_0_8 : !felt.type<"bn128">, !felt.type<"bn128">
          %20 = cast.toindex %arg4 : !felt.type<"bn128">
          %21 = array.read %2[%20] : <11 x !felt.type<"bn128">>, !felt.type<"bn128">
          %22 = felt.mul %21, %felt_const_1_3 : !felt.type<"bn128">, !felt.type<"bn128">
          %23 = felt.add %arg2, %22 : !felt.type<"bn128">, !felt.type<"bn128">
          %24 = felt.add %arg3, %arg3 : !felt.type<"bn128">, !felt.type<"bn128">
          %felt_const_1_9 = felt.const  1 : <"bn128">
          %25 = felt.add %arg4, %felt_const_1_9 : !felt.type<"bn128">, !felt.type<"bn128">
          scf.yield %23, %24, %25 : !felt.type<"bn128">, !felt.type<"bn128">, !felt.type<"bn128">
        }
        constrain.eq %10#0, %1 : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_1_5 = felt.const  1 : <"bn128">
        %felt_const_10_6 = felt.const  10 : <"bn128">
        %11 = cast.toindex %felt_const_10_6 : !felt.type<"bn128">
        %12 = array.read %2[%11] : <11 x !felt.type<"bn128">>, !felt.type<"bn128">
        %13 = felt.sub %felt_const_1_5, %12 : !felt.type<"bn128">, !felt.type<"bn128">
        constrain.eq %0, %13 : !felt.type<"bn128">, !felt.type<"bn128">
        function.return
      }
    }
  }
}
