module attributes {llzk.lang = "circom", llzk.main = !struct.type<@SignFp_1::@SignFp_1<[]>>} {
  poly.template @Num2Bits_0 {
    struct.def @Num2Bits_0 {
      struct.member @out : !array.type<64 x !felt.type<"bn128">> {llzk.pub}
      function.def @compute(%arg0: !felt.type<"bn128"> {function.arg_name = "in"}) -> !struct.type<@Num2Bits_0::@Num2Bits_0<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@Num2Bits_0::@Num2Bits_0<[]>>
        %nondet = llzk.nondet : !array.type<64 x !felt.type<"bn128">>
        %felt_const_64 = felt.const  64 : <"bn128">
        %felt_const_0 = felt.const  0 : <"bn128">
        %felt_const_1 = felt.const  1 : <"bn128">
        %felt_const_0_0 = felt.const  0 : <"bn128">
        %0:3 = scf.while (%arg1 = %felt_const_1, %arg2 = %felt_const_0, %arg3 = %felt_const_0_0) : (!felt.type<"bn128">, !felt.type<"bn128">, !felt.type<"bn128">) -> (!felt.type<"bn128">, !felt.type<"bn128">, !felt.type<"bn128">) {
          %felt_const_64_1 = felt.const  64 : <"bn128">
          %1 = bool.cmp lt(%arg3, %felt_const_64_1) : !felt.type<"bn128">, !felt.type<"bn128">
          scf.condition(%1) %arg1, %arg2, %arg3 : !felt.type<"bn128">, !felt.type<"bn128">, !felt.type<"bn128">
        } do {
        ^bb0(%arg1: !felt.type<"bn128">, %arg2: !felt.type<"bn128">, %arg3: !felt.type<"bn128">):
          %1 = felt.shr %arg0, %arg3 : !felt.type<"bn128">, !felt.type<"bn128">
          %felt_const_1_1 = felt.const  1 : <"bn128">
          %2 = felt.bit_and %1, %felt_const_1_1 : !felt.type<"bn128">, !felt.type<"bn128">
          %3 = cast.toindex %arg3 : !felt.type<"bn128">
          array.write %nondet[%3] = %2 : <64 x !felt.type<"bn128">>, !felt.type<"bn128">
          %4 = cast.toindex %arg3 : !felt.type<"bn128">
          %5 = array.read %nondet[%4] : <64 x !felt.type<"bn128">>, !felt.type<"bn128">
          %6 = felt.mul %5, %arg1 : !felt.type<"bn128">, !felt.type<"bn128">
          %7 = felt.add %arg2, %6 : !felt.type<"bn128">, !felt.type<"bn128">
          %8 = felt.add %arg1, %arg1 : !felt.type<"bn128">, !felt.type<"bn128">
          %felt_const_1_2 = felt.const  1 : <"bn128">
          %9 = felt.add %arg3, %felt_const_1_2 : !felt.type<"bn128">, !felt.type<"bn128">
          scf.yield %8, %7, %9 : !felt.type<"bn128">, !felt.type<"bn128">, !felt.type<"bn128">
        }
        struct.writem %self[@out] = %nondet : <@Num2Bits_0::@Num2Bits_0<[]>>, !array.type<64 x !felt.type<"bn128">>
        function.return %self : !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, %arg1: !felt.type<"bn128"> {function.arg_name = "in"}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@out] : <@Num2Bits_0::@Num2Bits_0<[]>>, !array.type<64 x !felt.type<"bn128">>
        %felt_const_64 = felt.const  64 : <"bn128">
        %felt_const_0 = felt.const  0 : <"bn128">
        %felt_const_1 = felt.const  1 : <"bn128">
        %felt_const_0_0 = felt.const  0 : <"bn128">
        %1:3 = scf.while (%arg2 = %felt_const_0, %arg3 = %felt_const_1, %arg4 = %felt_const_0_0) : (!felt.type<"bn128">, !felt.type<"bn128">, !felt.type<"bn128">) -> (!felt.type<"bn128">, !felt.type<"bn128">, !felt.type<"bn128">) {
          %felt_const_64_1 = felt.const  64 : <"bn128">
          %2 = bool.cmp lt(%arg4, %felt_const_64_1) : !felt.type<"bn128">, !felt.type<"bn128">
          scf.condition(%2) %arg2, %arg3, %arg4 : !felt.type<"bn128">, !felt.type<"bn128">, !felt.type<"bn128">
        } do {
        ^bb0(%arg2: !felt.type<"bn128">, %arg3: !felt.type<"bn128">, %arg4: !felt.type<"bn128">):
          %2 = cast.toindex %arg4 : !felt.type<"bn128">
          %3 = array.read %0[%2] : <64 x !felt.type<"bn128">>, !felt.type<"bn128">
          %4 = cast.toindex %arg4 : !felt.type<"bn128">
          %5 = array.read %0[%4] : <64 x !felt.type<"bn128">>, !felt.type<"bn128">
          %felt_const_1_1 = felt.const  1 : <"bn128">
          %6 = felt.sub %5, %felt_const_1_1 : !felt.type<"bn128">, !felt.type<"bn128">
          %7 = felt.mul %3, %6 : !felt.type<"bn128">, !felt.type<"bn128">
          %felt_const_0_2 = felt.const  0 : <"bn128">
          constrain.eq %7, %felt_const_0_2 : !felt.type<"bn128">, !felt.type<"bn128">
          %8 = cast.toindex %arg4 : !felt.type<"bn128">
          %9 = array.read %0[%8] : <64 x !felt.type<"bn128">>, !felt.type<"bn128">
          %10 = felt.mul %9, %arg3 : !felt.type<"bn128">, !felt.type<"bn128">
          %11 = felt.add %arg2, %10 : !felt.type<"bn128">, !felt.type<"bn128">
          %12 = felt.add %arg3, %arg3 : !felt.type<"bn128">, !felt.type<"bn128">
          %felt_const_1_3 = felt.const  1 : <"bn128">
          %13 = felt.add %arg4, %felt_const_1_3 : !felt.type<"bn128">, !felt.type<"bn128">
          scf.yield %11, %12, %13 : !felt.type<"bn128">, !felt.type<"bn128">, !felt.type<"bn128">
        }
        constrain.eq %1#0, %arg1 : !felt.type<"bn128">, !felt.type<"bn128">
        function.return
      }
    }
  }
  poly.template @SignFp_1 {
    struct.def @SignFp_1 {
      struct.member @sign : !felt.type<"bn128"> {llzk.pub}
      struct.member @a_bits : !array.type<64 x !felt.type<"bn128">>
      struct.member @Num2Bits_5_100 : !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
      struct.member @Num2Bits_5_100$inputs : !pod.type<[@in: !felt.type<"bn128">]>
      function.def @compute(%arg0: !felt.type<"bn128"> {function.arg_name = "a"}) -> !struct.type<@SignFp_1::@SignFp_1<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@SignFp_1::@SignFp_1<[]>>
        %pod = pod.new : <[]>
        %c1 = arith.constant 1 : index
        %pod_0 = pod.new { @count = %c1, @params = %pod }  : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>
        %pod_1 = pod.new : <[@in: !felt.type<"bn128">]>
        pod.write %pod_1[@in] = %arg0 : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        %0 = pod.read %pod_0[@count] : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>, index
        %c1_2 = arith.constant 1 : index
        %1 = arith.subi %0, %c1_2 : index
        pod.write %pod_0[@count] = %1 : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>, index
        %c0 = arith.constant 0 : index
        %2 = arith.cmpi eq, %1, %c0 : index
        scf.if %2 {
          %8 = pod.read %pod_0[@params] : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>, !pod.type<[]>
          %9 = pod.read %pod_1[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
          %10 = function.call @Num2Bits_0::@Num2Bits_0::@compute(%9) : (!felt.type<"bn128">) -> !struct.type<@Num2Bits_0::@Num2Bits_0<[]>> 
          pod.write %pod_0[@comp] = %10 : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>, !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
        }
        %3 = pod.read %pod_0[@comp] : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>, !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
        %4 = struct.readm %3[@out] : <@Num2Bits_0::@Num2Bits_0<[]>>, !array.type<64 x !felt.type<"bn128">>
        struct.writem %self[@a_bits] = %4 : <@SignFp_1::@SignFp_1<[]>>, !array.type<64 x !felt.type<"bn128">>
        %felt_const_0 = felt.const  0 : <"bn128">
        %5 = cast.toindex %felt_const_0 : !felt.type<"bn128">
        %6 = array.read %4[%5] : <64 x !felt.type<"bn128">>, !felt.type<"bn128">
        struct.writem %self[@sign] = %6 : <@SignFp_1::@SignFp_1<[]>>, !felt.type<"bn128">
        struct.writem %self[@Num2Bits_5_100$inputs] = %pod_1 : <@SignFp_1::@SignFp_1<[]>>, !pod.type<[@in: !felt.type<"bn128">]>
        %7 = pod.read %pod_0[@comp] : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>, !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
        struct.writem %self[@Num2Bits_5_100] = %7 : <@SignFp_1::@SignFp_1<[]>>, !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
        function.return %self : !struct.type<@SignFp_1::@SignFp_1<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@SignFp_1::@SignFp_1<[]>>, %arg1: !felt.type<"bn128"> {function.arg_name = "a"}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@sign] : <@SignFp_1::@SignFp_1<[]>>, !felt.type<"bn128">
        %1 = struct.readm %arg0[@a_bits] : <@SignFp_1::@SignFp_1<[]>>, !array.type<64 x !felt.type<"bn128">>
        %2 = struct.readm %arg0[@Num2Bits_5_100] : <@SignFp_1::@SignFp_1<[]>>, !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
        %3 = struct.readm %arg0[@Num2Bits_5_100$inputs] : <@SignFp_1::@SignFp_1<[]>>, !pod.type<[@in: !felt.type<"bn128">]>
        %4 = pod.read %3[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        constrain.eq %4, %arg1 : !felt.type<"bn128">, !felt.type<"bn128">
        %5 = struct.readm %2[@out] : <@Num2Bits_0::@Num2Bits_0<[]>>, !array.type<64 x !felt.type<"bn128">>
        constrain.eq %1, %5 : !array.type<64 x !felt.type<"bn128">>, !array.type<64 x !felt.type<"bn128">>
        %felt_const_0 = felt.const  0 : <"bn128">
        %6 = cast.toindex %felt_const_0 : !felt.type<"bn128">
        %7 = array.read %1[%6] : <64 x !felt.type<"bn128">>, !felt.type<"bn128">
        constrain.eq %0, %7 : !felt.type<"bn128">, !felt.type<"bn128">
        %8 = pod.read %3[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        function.call @Num2Bits_0::@Num2Bits_0::@constrain(%2, %8) : (!struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, !felt.type<"bn128">) -> () 
        function.return
      }
    }
  }
}
