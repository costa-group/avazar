module attributes {llzk.lang = "circom", llzk.main = !struct.type<@Num2Ternary_1::@Num2Ternary_1<[]>>} {
  poly.template @Num2Bits_0 {
    struct.def @Num2Bits_0 {
      struct.member @out : !array.type<2 x !felt.type<"goldilocks">> {llzk.pub}
      function.def @compute(%arg0: !felt.type<"goldilocks"> {function.arg_name = "in"}) -> !struct.type<@Num2Bits_0::@Num2Bits_0<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@Num2Bits_0::@Num2Bits_0<[]>>
        %nondet = llzk.nondet : !array.type<2 x !felt.type<"goldilocks">>
        %felt_const_2 = felt.const  2 : <"goldilocks">
        %felt_const_0 = felt.const  0 : <"goldilocks">
        %felt_const_1 = felt.const  1 : <"goldilocks">
        %felt_const_0_0 = felt.const  0 : <"goldilocks">
        %0:3 = scf.while (%arg1 = %felt_const_0, %arg2 = %felt_const_1, %arg3 = %felt_const_0_0) : (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">) -> (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">) {
          %felt_const_2_1 = felt.const  2 : <"goldilocks">
          %1 = bool.cmp lt(%arg3, %felt_const_2_1) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.condition(%1) %arg1, %arg2, %arg3 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">
        } do {
        ^bb0(%arg1: !felt.type<"goldilocks">, %arg2: !felt.type<"goldilocks">, %arg3: !felt.type<"goldilocks">):
          %1 = felt.shr %arg0, %arg3 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_1 = felt.const  1 : <"goldilocks">
          %2 = felt.bit_and %1, %felt_const_1_1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %3 = cast.toindex %arg3 : !felt.type<"goldilocks">
          array.write %nondet[%3] = %2 : <2 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %4 = cast.toindex %arg3 : !felt.type<"goldilocks">
          %5 = array.read %nondet[%4] : <2 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %6 = felt.mul %5, %arg2 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %7 = felt.add %arg1, %6 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %8 = felt.add %arg2, %arg2 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_2 = felt.const  1 : <"goldilocks">
          %9 = felt.add %arg3, %felt_const_1_2 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.yield %7, %8, %9 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">
        }
        struct.writem %self[@out] = %nondet : <@Num2Bits_0::@Num2Bits_0<[]>>, !array.type<2 x !felt.type<"goldilocks">>
        function.return %self : !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, %arg1: !felt.type<"goldilocks"> {function.arg_name = "in"}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@out] : <@Num2Bits_0::@Num2Bits_0<[]>>, !array.type<2 x !felt.type<"goldilocks">>
        %felt_const_2 = felt.const  2 : <"goldilocks">
        %felt_const_0 = felt.const  0 : <"goldilocks">
        %felt_const_1 = felt.const  1 : <"goldilocks">
        %felt_const_0_0 = felt.const  0 : <"goldilocks">
        %1:3 = scf.while (%arg2 = %felt_const_0_0, %arg3 = %felt_const_0, %arg4 = %felt_const_1) : (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">) -> (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">) {
          %felt_const_2_1 = felt.const  2 : <"goldilocks">
          %2 = bool.cmp lt(%arg2, %felt_const_2_1) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.condition(%2) %arg2, %arg3, %arg4 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">
        } do {
        ^bb0(%arg2: !felt.type<"goldilocks">, %arg3: !felt.type<"goldilocks">, %arg4: !felt.type<"goldilocks">):
          %2 = cast.toindex %arg2 : !felt.type<"goldilocks">
          %3 = array.read %0[%2] : <2 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %4 = cast.toindex %arg2 : !felt.type<"goldilocks">
          %5 = array.read %0[%4] : <2 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %felt_const_1_1 = felt.const  1 : <"goldilocks">
          %6 = felt.sub %5, %felt_const_1_1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %7 = felt.mul %3, %6 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_0_2 = felt.const  0 : <"goldilocks">
          constrain.eq %7, %felt_const_0_2 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %8 = cast.toindex %arg2 : !felt.type<"goldilocks">
          %9 = array.read %0[%8] : <2 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %10 = felt.mul %9, %arg4 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %11 = felt.add %arg3, %10 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %12 = felt.add %arg4, %arg4 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_3 = felt.const  1 : <"goldilocks">
          %13 = felt.add %arg2, %felt_const_1_3 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.yield %13, %11, %12 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">
        }
        constrain.eq %1#1, %arg1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        function.return
      }
    }
  }
  poly.template @Num2Ternary_1 {
    struct.def @Num2Ternary_1 {
      struct.member @out : !array.type<2,2 x !felt.type<"goldilocks">> {llzk.pub}
      struct.member @ternary_digits : !array.type<2 x !felt.type<"goldilocks">>
      struct.member @Num2Bits_14_307 : !array.type<2 x !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>>
      struct.member @Num2Bits_14_307$inputs : !array.type<2 x !pod.type<[@in: !felt.type<"goldilocks">]>>
      function.def @compute(%arg0: !felt.type<"goldilocks"> {function.arg_name = "in"}) -> !struct.type<@Num2Ternary_1::@Num2Ternary_1<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@Num2Ternary_1::@Num2Ternary_1<[]>>
        %nondet = llzk.nondet : !array.type<2 x !felt.type<"goldilocks">>
        %nondet_0 = llzk.nondet : !array.type<2,2 x !felt.type<"goldilocks">>
        %array = array.new  : <2 x !pod.type<[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>> 
        %pod = pod.new : <[]>
        %c2 = arith.constant 2 : index
        %c0 = arith.constant 0 : index
        %c1 = arith.constant 1 : index
        scf.for %arg1 = %c0 to %c2 step %c1 {
          %c1_8 = arith.constant 1 : index
          %pod_9 = pod.new { @count = %c1_8, @params = %pod }  : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>
          array.write %array[%arg1] = %pod_9 : <2 x !pod.type<[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>>, !pod.type<[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>
        }
        %array_1 = array.new  : <2 x !pod.type<[@in: !felt.type<"goldilocks">]>> 
        %felt_const_2 = felt.const  2 : <"goldilocks">
        %felt_const_0 = felt.const  0 : <"goldilocks">
        %felt_const_0_2 = felt.const  0 : <"goldilocks">
        %felt_const_1 = felt.const  1 : <"goldilocks">
        %felt_const_0_3 = felt.const  0 : <"goldilocks">
        %0:5 = scf.while (%arg1 = %felt_const_0_3, %arg2 = %felt_const_0, %arg3 = %felt_const_1, %arg4 = %array_1, %arg5 = %felt_const_0_2) : (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !array.type<2 x !pod.type<[@in: !felt.type<"goldilocks">]>>, !felt.type<"goldilocks">) -> (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !array.type<2 x !pod.type<[@in: !felt.type<"goldilocks">]>>, !felt.type<"goldilocks">) {
          %felt_const_2_8 = felt.const  2 : <"goldilocks">
          %1 = bool.cmp lt(%arg1, %felt_const_2_8) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.condition(%1) %arg1, %arg2, %arg3, %arg4, %arg5 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !array.type<2 x !pod.type<[@in: !felt.type<"goldilocks">]>>, !felt.type<"goldilocks">
        } do {
        ^bb0(%arg1: !felt.type<"goldilocks">, %arg2: !felt.type<"goldilocks">, %arg3: !felt.type<"goldilocks">, %arg4: !array.type<2 x !pod.type<[@in: !felt.type<"goldilocks">]>>, %arg5: !felt.type<"goldilocks">):
          %1 = felt.uintdiv %arg0, %arg3 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_3 = felt.const  3 : <"goldilocks">
          %2 = felt.umod %1, %felt_const_3 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %3 = cast.toindex %arg1 : !felt.type<"goldilocks">
          array.write %nondet[%3] = %2 : <2 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %4 = cast.toindex %arg1 : !felt.type<"goldilocks">
          %5 = array.read %nondet[%4] : <2 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %6 = felt.mul %5, %arg3 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %7 = felt.add %arg5, %6 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_3_8 = felt.const  3 : <"goldilocks">
          %8 = felt.mul %arg3, %felt_const_3_8 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %9 = cast.toindex %arg1 : !felt.type<"goldilocks">
          %10 = array.read %nondet[%9] : <2 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %11 = cast.toindex %arg2 : !felt.type<"goldilocks">
          %12 = array.read %arg4[%11] : <2 x !pod.type<[@in: !felt.type<"goldilocks">]>>, !pod.type<[@in: !felt.type<"goldilocks">]>
          pod.write %12[@in] = %10 : <[@in: !felt.type<"goldilocks">]>, !felt.type<"goldilocks">
          %13 = cast.toindex %arg2 : !felt.type<"goldilocks">
          array.write %arg4[%13] = %12 : <2 x !pod.type<[@in: !felt.type<"goldilocks">]>>, !pod.type<[@in: !felt.type<"goldilocks">]>
          %14 = cast.toindex %arg2 : !felt.type<"goldilocks">
          %15 = array.read %array[%14] : <2 x !pod.type<[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>>, !pod.type<[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>
          %16 = cast.toindex %arg2 : !felt.type<"goldilocks">
          %17 = array.read %arg4[%16] : <2 x !pod.type<[@in: !felt.type<"goldilocks">]>>, !pod.type<[@in: !felt.type<"goldilocks">]>
          %18 = pod.read %15[@count] : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>, index
          %c1_9 = arith.constant 1 : index
          %19 = arith.subi %18, %c1_9 : index
          pod.write %15[@count] = %19 : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>, index
          %c0_10 = arith.constant 0 : index
          %20 = arith.cmpi eq, %19, %c0_10 : index
          scf.if %20 {
            %28 = pod.read %15[@params] : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>, !pod.type<[]>
            %29 = pod.read %17[@in] : <[@in: !felt.type<"goldilocks">]>, !felt.type<"goldilocks">
            %30 = function.call @Num2Bits_0::@Num2Bits_0::@compute(%29) : (!felt.type<"goldilocks">) -> !struct.type<@Num2Bits_0::@Num2Bits_0<[]>> 
            pod.write %15[@comp] = %30 : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>, !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
            %31 = cast.toindex %arg2 : !felt.type<"goldilocks">
            array.write %array[%31] = %15 : <2 x !pod.type<[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>>, !pod.type<[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>
          }
          %21 = cast.toindex %arg2 : !felt.type<"goldilocks">
          %22 = array.read %array[%21] : <2 x !pod.type<[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>>, !pod.type<[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>
          %23 = pod.read %22[@comp] : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>, !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
          %24 = struct.readm %23[@out] : <@Num2Bits_0::@Num2Bits_0<[]>>, !array.type<2 x !felt.type<"goldilocks">>
          %25 = cast.toindex %arg1 : !felt.type<"goldilocks">
          array.insert %nondet_0[%25] = %24 : <2,2 x !felt.type<"goldilocks">>, <2 x !felt.type<"goldilocks">>
          %felt_const_1_11 = felt.const  1 : <"goldilocks">
          %26 = felt.add %arg1, %felt_const_1_11 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_12 = felt.const  1 : <"goldilocks">
          %27 = felt.add %arg2, %felt_const_1_12 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.yield %26, %27, %8, %arg4, %7 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !array.type<2 x !pod.type<[@in: !felt.type<"goldilocks">]>>, !felt.type<"goldilocks">
        }
        struct.writem %self[@Num2Bits_14_307$inputs] = %0#3 : <@Num2Ternary_1::@Num2Ternary_1<[]>>, !array.type<2 x !pod.type<[@in: !felt.type<"goldilocks">]>>
        %array_4 = array.new  : <2 x !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>> 
        %c2_5 = arith.constant 2 : index
        %c0_6 = arith.constant 0 : index
        %c1_7 = arith.constant 1 : index
        scf.for %arg1 = %c0_6 to %c2_5 step %c1_7 {
          %1 = array.read %array[%arg1] : <2 x !pod.type<[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>>, !pod.type<[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>
          %2 = pod.read %1[@comp] : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>, !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
          array.write %array_4[%arg1] = %2 : <2 x !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>>, !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
        }
        struct.writem %self[@Num2Bits_14_307] = %array_4 : <@Num2Ternary_1::@Num2Ternary_1<[]>>, !array.type<2 x !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>>
        struct.writem %self[@ternary_digits] = %nondet : <@Num2Ternary_1::@Num2Ternary_1<[]>>, !array.type<2 x !felt.type<"goldilocks">>
        struct.writem %self[@out] = %nondet_0 : <@Num2Ternary_1::@Num2Ternary_1<[]>>, !array.type<2,2 x !felt.type<"goldilocks">>
        function.return %self : !struct.type<@Num2Ternary_1::@Num2Ternary_1<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@Num2Ternary_1::@Num2Ternary_1<[]>>, %arg1: !felt.type<"goldilocks"> {function.arg_name = "in"}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@out] : <@Num2Ternary_1::@Num2Ternary_1<[]>>, !array.type<2,2 x !felt.type<"goldilocks">>
        %1 = struct.readm %arg0[@ternary_digits] : <@Num2Ternary_1::@Num2Ternary_1<[]>>, !array.type<2 x !felt.type<"goldilocks">>
        %2 = struct.readm %arg0[@Num2Bits_14_307] : <@Num2Ternary_1::@Num2Ternary_1<[]>>, !array.type<2 x !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>>
        %3 = struct.readm %arg0[@Num2Bits_14_307$inputs] : <@Num2Ternary_1::@Num2Ternary_1<[]>>, !array.type<2 x !pod.type<[@in: !felt.type<"goldilocks">]>>
        %felt_const_2 = felt.const  2 : <"goldilocks">
        %felt_const_0 = felt.const  0 : <"goldilocks">
        %felt_const_0_0 = felt.const  0 : <"goldilocks">
        %felt_const_1 = felt.const  1 : <"goldilocks">
        %felt_const_0_1 = felt.const  0 : <"goldilocks">
        %4:4 = scf.while (%arg2 = %felt_const_0_0, %arg3 = %felt_const_0, %arg4 = %felt_const_0_1, %arg5 = %felt_const_1) : (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">) -> (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">) {
          %felt_const_2_2 = felt.const  2 : <"goldilocks">
          %5 = bool.cmp lt(%arg4, %felt_const_2_2) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.condition(%5) %arg2, %arg3, %arg4, %arg5 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">
        } do {
        ^bb0(%arg2: !felt.type<"goldilocks">, %arg3: !felt.type<"goldilocks">, %arg4: !felt.type<"goldilocks">, %arg5: !felt.type<"goldilocks">):
          %5 = cast.toindex %arg4 : !felt.type<"goldilocks">
          %6 = array.read %1[%5] : <2 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %7 = felt.mul %6, %arg5 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %8 = felt.add %arg2, %7 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_3 = felt.const  3 : <"goldilocks">
          %9 = felt.mul %arg5, %felt_const_3 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %10 = cast.toindex %arg4 : !felt.type<"goldilocks">
          %11 = array.read %1[%10] : <2 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %12 = cast.toindex %arg3 : !felt.type<"goldilocks">
          %13 = array.read %3[%12] : <2 x !pod.type<[@in: !felt.type<"goldilocks">]>>, !pod.type<[@in: !felt.type<"goldilocks">]>
          %14 = pod.read %13[@in] : <[@in: !felt.type<"goldilocks">]>, !felt.type<"goldilocks">
          constrain.eq %14, %11 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %15 = cast.toindex %arg3 : !felt.type<"goldilocks">
          %16 = array.read %2[%15] : <2 x !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>>, !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
          %17 = struct.readm %16[@out] : <@Num2Bits_0::@Num2Bits_0<[]>>, !array.type<2 x !felt.type<"goldilocks">>
          %18 = cast.toindex %arg4 : !felt.type<"goldilocks">
          %19 = array.extract %0[%18] : <2,2 x !felt.type<"goldilocks">>
          constrain.eq %19, %17 : !array.type<2 x !felt.type<"goldilocks">>, !array.type<2 x !felt.type<"goldilocks">>
          %20 = cast.toindex %arg4 : !felt.type<"goldilocks">
          %felt_const_0_2 = felt.const  0 : <"goldilocks">
          %21 = cast.toindex %felt_const_0_2 : !felt.type<"goldilocks">
          %22 = array.read %0[%20, %21] : <2,2 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %23 = cast.toindex %arg4 : !felt.type<"goldilocks">
          %felt_const_1_3 = felt.const  1 : <"goldilocks">
          %24 = cast.toindex %felt_const_1_3 : !felt.type<"goldilocks">
          %25 = array.read %0[%23, %24] : <2,2 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %26 = felt.mul %22, %25 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_0_4 = felt.const  0 : <"goldilocks">
          constrain.eq %26, %felt_const_0_4 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_5 = felt.const  1 : <"goldilocks">
          %27 = felt.add %arg4, %felt_const_1_5 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_6 = felt.const  1 : <"goldilocks">
          %28 = felt.add %arg3, %felt_const_1_6 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.yield %8, %28, %27, %9 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">
        }
        constrain.eq %4#0, %arg1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        %c2 = arith.constant 2 : index
        %c0 = arith.constant 0 : index
        %c1 = arith.constant 1 : index
        scf.for %arg2 = %c0 to %c2 step %c1 {
          %5 = array.read %2[%arg2] : <2 x !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>>, !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
          %6 = array.read %3[%arg2] : <2 x !pod.type<[@in: !felt.type<"goldilocks">]>>, !pod.type<[@in: !felt.type<"goldilocks">]>
          %7 = pod.read %6[@in] : <[@in: !felt.type<"goldilocks">]>, !felt.type<"goldilocks">
          function.call @Num2Bits_0::@Num2Bits_0::@constrain(%5, %7) : (!struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, !felt.type<"goldilocks">) -> () 
        }
        function.return
      }
    }
  }
}
