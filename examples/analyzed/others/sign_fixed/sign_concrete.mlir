module attributes {llzk.lang = "circom", llzk.main = !struct.type<@SignFp_5::@SignFp_5<[]>>} {
  poly.template @Num2Bits_0 {
    struct.def @Num2Bits_0 {
      struct.member @out : !array.type<64 x !felt.type<"goldilocks">> {llzk.pub}
      function.def @compute(%arg0: !felt.type<"goldilocks"> {function.arg_name = "in"}) -> !struct.type<@Num2Bits_0::@Num2Bits_0<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@Num2Bits_0::@Num2Bits_0<[]>>
        %nondet = llzk.nondet : !array.type<64 x !felt.type<"goldilocks">>
        %felt_const_64 = felt.const  64 : <"goldilocks">
        %felt_const_0 = felt.const  0 : <"goldilocks">
        %felt_const_1 = felt.const  1 : <"goldilocks">
        %felt_const_0_0 = felt.const  0 : <"goldilocks">
        %0:3 = scf.while (%arg1 = %felt_const_0, %arg2 = %felt_const_0_0, %arg3 = %felt_const_1) : (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">) -> (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">) {
          %felt_const_64_1 = felt.const  64 : <"goldilocks">
          %1 = bool.cmp lt(%arg2, %felt_const_64_1) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.condition(%1) %arg1, %arg2, %arg3 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">
        } do {
        ^bb0(%arg1: !felt.type<"goldilocks">, %arg2: !felt.type<"goldilocks">, %arg3: !felt.type<"goldilocks">):
          %1 = felt.shr %arg0, %arg2 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_1 = felt.const  1 : <"goldilocks">
          %2 = felt.bit_and %1, %felt_const_1_1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %3 = cast.toindex %arg2 : !felt.type<"goldilocks">
          array.write %nondet[%3] = %2 : <64 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %4 = cast.toindex %arg2 : !felt.type<"goldilocks">
          %5 = array.read %nondet[%4] : <64 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %6 = felt.mul %5, %arg3 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %7 = felt.add %arg1, %6 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %8 = felt.add %arg3, %arg3 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_2 = felt.const  1 : <"goldilocks">
          %9 = felt.add %arg2, %felt_const_1_2 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.yield %7, %9, %8 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">
        }
        struct.writem %self[@out] = %nondet : <@Num2Bits_0::@Num2Bits_0<[]>>, !array.type<64 x !felt.type<"goldilocks">>
        function.return %self : !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, %arg1: !felt.type<"goldilocks"> {function.arg_name = "in"}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@out] : <@Num2Bits_0::@Num2Bits_0<[]>>, !array.type<64 x !felt.type<"goldilocks">>
        %felt_const_64 = felt.const  64 : <"goldilocks">
        %felt_const_0 = felt.const  0 : <"goldilocks">
        %felt_const_1 = felt.const  1 : <"goldilocks">
        %felt_const_0_0 = felt.const  0 : <"goldilocks">
        %1:3 = scf.while (%arg2 = %felt_const_1, %arg3 = %felt_const_0_0, %arg4 = %felt_const_0) : (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">) -> (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">) {
          %felt_const_64_1 = felt.const  64 : <"goldilocks">
          %2 = bool.cmp lt(%arg3, %felt_const_64_1) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.condition(%2) %arg2, %arg3, %arg4 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">
        } do {
        ^bb0(%arg2: !felt.type<"goldilocks">, %arg3: !felt.type<"goldilocks">, %arg4: !felt.type<"goldilocks">):
          %2 = cast.toindex %arg3 : !felt.type<"goldilocks">
          %3 = array.read %0[%2] : <64 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %4 = cast.toindex %arg3 : !felt.type<"goldilocks">
          %5 = array.read %0[%4] : <64 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %felt_const_1_1 = felt.const  1 : <"goldilocks">
          %6 = felt.sub %5, %felt_const_1_1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %7 = felt.mul %3, %6 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_0_2 = felt.const  0 : <"goldilocks">
          constrain.eq %7, %felt_const_0_2 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %8 = cast.toindex %arg3 : !felt.type<"goldilocks">
          %9 = array.read %0[%8] : <64 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %10 = felt.mul %9, %arg2 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %11 = felt.add %arg4, %10 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %12 = felt.add %arg2, %arg2 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_3 = felt.const  1 : <"goldilocks">
          %13 = felt.add %arg3, %felt_const_1_3 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.yield %12, %13, %11 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">
        }
        constrain.eq %1#2, %arg1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        function.return
      }
    }
  }
  poly.template @Num2Bits_1 {
    struct.def @Num2Bits_1 {
      struct.member @out : !array.type<33 x !felt.type<"goldilocks">> {llzk.pub}
      function.def @compute(%arg0: !felt.type<"goldilocks"> {function.arg_name = "in"}) -> !struct.type<@Num2Bits_1::@Num2Bits_1<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@Num2Bits_1::@Num2Bits_1<[]>>
        %nondet = llzk.nondet : !array.type<33 x !felt.type<"goldilocks">>
        %felt_const_33 = felt.const  33 : <"goldilocks">
        %felt_const_0 = felt.const  0 : <"goldilocks">
        %felt_const_1 = felt.const  1 : <"goldilocks">
        %felt_const_0_0 = felt.const  0 : <"goldilocks">
        %0:3 = scf.while (%arg1 = %felt_const_0_0, %arg2 = %felt_const_0, %arg3 = %felt_const_1) : (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">) -> (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">) {
          %felt_const_33_1 = felt.const  33 : <"goldilocks">
          %1 = bool.cmp lt(%arg1, %felt_const_33_1) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.condition(%1) %arg1, %arg2, %arg3 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">
        } do {
        ^bb0(%arg1: !felt.type<"goldilocks">, %arg2: !felt.type<"goldilocks">, %arg3: !felt.type<"goldilocks">):
          %1 = felt.shr %arg0, %arg1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_1 = felt.const  1 : <"goldilocks">
          %2 = felt.bit_and %1, %felt_const_1_1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %3 = cast.toindex %arg1 : !felt.type<"goldilocks">
          array.write %nondet[%3] = %2 : <33 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %4 = cast.toindex %arg1 : !felt.type<"goldilocks">
          %5 = array.read %nondet[%4] : <33 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %6 = felt.mul %5, %arg3 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %7 = felt.add %arg2, %6 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %8 = felt.add %arg3, %arg3 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_2 = felt.const  1 : <"goldilocks">
          %9 = felt.add %arg1, %felt_const_1_2 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.yield %9, %7, %8 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">
        }
        struct.writem %self[@out] = %nondet : <@Num2Bits_1::@Num2Bits_1<[]>>, !array.type<33 x !felt.type<"goldilocks">>
        function.return %self : !struct.type<@Num2Bits_1::@Num2Bits_1<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@Num2Bits_1::@Num2Bits_1<[]>>, %arg1: !felt.type<"goldilocks"> {function.arg_name = "in"}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@out] : <@Num2Bits_1::@Num2Bits_1<[]>>, !array.type<33 x !felt.type<"goldilocks">>
        %felt_const_33 = felt.const  33 : <"goldilocks">
        %felt_const_0 = felt.const  0 : <"goldilocks">
        %felt_const_1 = felt.const  1 : <"goldilocks">
        %felt_const_0_0 = felt.const  0 : <"goldilocks">
        %1:3 = scf.while (%arg2 = %felt_const_1, %arg3 = %felt_const_0, %arg4 = %felt_const_0_0) : (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">) -> (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">) {
          %felt_const_33_1 = felt.const  33 : <"goldilocks">
          %2 = bool.cmp lt(%arg4, %felt_const_33_1) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.condition(%2) %arg2, %arg3, %arg4 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">
        } do {
        ^bb0(%arg2: !felt.type<"goldilocks">, %arg3: !felt.type<"goldilocks">, %arg4: !felt.type<"goldilocks">):
          %2 = cast.toindex %arg4 : !felt.type<"goldilocks">
          %3 = array.read %0[%2] : <33 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %4 = cast.toindex %arg4 : !felt.type<"goldilocks">
          %5 = array.read %0[%4] : <33 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %felt_const_1_1 = felt.const  1 : <"goldilocks">
          %6 = felt.sub %5, %felt_const_1_1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %7 = felt.mul %3, %6 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_0_2 = felt.const  0 : <"goldilocks">
          constrain.eq %7, %felt_const_0_2 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %8 = cast.toindex %arg4 : !felt.type<"goldilocks">
          %9 = array.read %0[%8] : <33 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %10 = felt.mul %9, %arg2 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %11 = felt.add %arg3, %10 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %12 = felt.add %arg2, %arg2 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_3 = felt.const  1 : <"goldilocks">
          %13 = felt.add %arg4, %felt_const_1_3 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.yield %12, %11, %13 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">
        }
        constrain.eq %1#1, %arg1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        function.return
      }
    }
  }
  poly.template @CompConstant_2 {
    struct.def @CompConstant_2 {
      struct.member @out : !felt.type<"goldilocks"> {llzk.pub}
      struct.member @parts : !array.type<32 x !felt.type<"goldilocks">>
      struct.member @sum : !array.type<32 x !felt.type<"goldilocks">>
      struct.member @num2bits : !array.type<33 x !felt.type<"goldilocks">>
      struct.member @Num2Bits_68_1294 : !struct.type<@Num2Bits_1::@Num2Bits_1<[]>>
      struct.member @Num2Bits_68_1294$inputs : !pod.type<[@in: !felt.type<"goldilocks">]>
      function.def @compute(%arg0: !array.type<64 x !felt.type<"goldilocks">> {function.arg_name = "in"}) -> !struct.type<@CompConstant_2::@CompConstant_2<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@CompConstant_2::@CompConstant_2<[]>>
        %nondet = llzk.nondet : !array.type<32 x !felt.type<"goldilocks">>
        %nondet_0 = llzk.nondet : !array.type<32 x !felt.type<"goldilocks">>
        %pod = pod.new : <[]>
        %c1 = arith.constant 1 : index
        %pod_1 = pod.new { @count = %c1, @params = %pod }  : <[@count: index, @comp: !struct.type<@Num2Bits_1::@Num2Bits_1<[]>>, @params: !pod.type<[]>]>
        %pod_2 = pod.new : <[@in: !felt.type<"goldilocks">]>
        %felt_const_18446744069414584320 = felt.const  18446744069414584320 : <"goldilocks">
        %felt_const_0 = felt.const  0 : <"goldilocks">
        %felt_const_0_3 = felt.const  0 : <"goldilocks">
        %felt_const_0_4 = felt.const  0 : <"goldilocks">
        %felt_const_0_5 = felt.const  0 : <"goldilocks">
        %felt_const_1 = felt.const  1 : <"goldilocks">
        %felt_const_0_6 = felt.const  0 : <"goldilocks">
        %felt_const_0_7 = felt.const  0 : <"goldilocks">
        %0:6 = scf.while (%arg1 = %felt_const_1, %arg2 = %felt_const_0_4, %arg3 = %felt_const_0_3, %arg4 = %felt_const_0_7, %arg5 = %felt_const_0_5, %arg6 = %felt_const_0) : (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">) -> (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">) {
          %felt_const_32_10 = felt.const  32 : <"goldilocks">
          %12 = bool.cmp lt(%arg4, %felt_const_32_10) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.condition(%12) %arg1, %arg2, %arg3, %arg4, %arg5, %arg6 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">
        } do {
        ^bb0(%arg1: !felt.type<"goldilocks">, %arg2: !felt.type<"goldilocks">, %arg3: !felt.type<"goldilocks">, %arg4: !felt.type<"goldilocks">, %arg5: !felt.type<"goldilocks">, %arg6: !felt.type<"goldilocks">):
          %felt_const_18446744069414584320_10 = felt.const  18446744069414584320 : <"goldilocks">
          %felt_const_2 = felt.const  2 : <"goldilocks">
          %12 = felt.mul %arg4, %felt_const_2 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %13 = felt.shr %felt_const_18446744069414584320_10, %12 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_11 = felt.const  1 : <"goldilocks">
          %14 = felt.bit_and %13, %felt_const_1_11 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_18446744069414584320_12 = felt.const  18446744069414584320 : <"goldilocks">
          %felt_const_2_13 = felt.const  2 : <"goldilocks">
          %15 = felt.mul %arg4, %felt_const_2_13 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_14 = felt.const  1 : <"goldilocks">
          %16 = felt.add %15, %felt_const_1_14 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %17 = felt.shr %felt_const_18446744069414584320_12, %16 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_15 = felt.const  1 : <"goldilocks">
          %18 = felt.bit_and %17, %felt_const_1_15 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_2_16 = felt.const  2 : <"goldilocks">
          %19 = felt.mul %arg4, %felt_const_2_16 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %20 = cast.toindex %19 : !felt.type<"goldilocks">
          %21 = array.read %arg0[%20] : <64 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %felt_const_2_17 = felt.const  2 : <"goldilocks">
          %22 = felt.mul %arg4, %felt_const_2_17 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_18 = felt.const  1 : <"goldilocks">
          %23 = felt.add %22, %felt_const_1_18 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %24 = cast.toindex %23 : !felt.type<"goldilocks">
          %25 = array.read %arg0[%24] : <64 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %felt_const_0_19 = felt.const  0 : <"goldilocks">
          %26 = bool.cmp eq(%18, %felt_const_0_19) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_0_20 = felt.const  0 : <"goldilocks">
          %27 = bool.cmp eq(%14, %felt_const_0_20) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %28 = bool.and %26, %27 : i1, i1
          scf.if %28 {
            %32 = felt.mul %25, %arg1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %33 = felt.mul %21, %arg1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %34 = felt.add %32, %33 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %35 = felt.mul %25, %21 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %36 = felt.mul %35, %arg1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %37 = felt.sub %34, %36 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %38 = cast.toindex %arg4 : !felt.type<"goldilocks">
            array.write %nondet_0[%38] = %37 : <32 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          } else {
            %32 = felt.mul %arg1, %25 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %33 = felt.mul %32, %21 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %34 = felt.sub %33, %arg1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %35 = cast.toindex %arg4 : !felt.type<"goldilocks">
            array.write %nondet_0[%35] = %34 : <32 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          }
          %felt_const_0_21 = felt.const  0 : <"goldilocks">
          %29 = bool.cmp eq(%arg4, %felt_const_0_21) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.if %29 {
            %felt_const_4294967295 = felt.const  4294967295 : <"goldilocks">
            %felt_const_0_24 = felt.const  0 : <"goldilocks">
            %32 = cast.toindex %felt_const_0_24 : !felt.type<"goldilocks">
            %33 = array.read %nondet_0[%32] : <32 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
            %34 = felt.add %felt_const_4294967295, %33 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %felt_const_0_25 = felt.const  0 : <"goldilocks">
            %35 = cast.toindex %felt_const_0_25 : !felt.type<"goldilocks">
            array.write %nondet[%35] = %34 : <32 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          } else {
            %felt_const_1_24 = felt.const  1 : <"goldilocks">
            %32 = felt.sub %arg4, %felt_const_1_24 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %33 = cast.toindex %32 : !felt.type<"goldilocks">
            %34 = array.read %nondet[%33] : <32 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
            %35 = cast.toindex %arg4 : !felt.type<"goldilocks">
            %36 = array.read %nondet_0[%35] : <32 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
            %37 = felt.add %34, %36 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %38 = cast.toindex %arg4 : !felt.type<"goldilocks">
            array.write %nondet[%38] = %37 : <32 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          }
          %felt_const_2_22 = felt.const  2 : <"goldilocks">
          %30 = felt.mul %arg1, %felt_const_2_22 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_23 = felt.const  1 : <"goldilocks">
          %31 = felt.add %arg4, %felt_const_1_23 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.yield %30, %21, %18, %31, %25, %14 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">
        }
        %felt_const_31 = felt.const  31 : <"goldilocks">
        %1 = cast.toindex %felt_const_31 : !felt.type<"goldilocks">
        %2 = array.read %nondet[%1] : <32 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
        pod.write %pod_2[@in] = %2 : <[@in: !felt.type<"goldilocks">]>, !felt.type<"goldilocks">
        %3 = pod.read %pod_1[@count] : <[@count: index, @comp: !struct.type<@Num2Bits_1::@Num2Bits_1<[]>>, @params: !pod.type<[]>]>, index
        %c1_8 = arith.constant 1 : index
        %4 = arith.subi %3, %c1_8 : index
        pod.write %pod_1[@count] = %4 : <[@count: index, @comp: !struct.type<@Num2Bits_1::@Num2Bits_1<[]>>, @params: !pod.type<[]>]>, index
        %c0 = arith.constant 0 : index
        %5 = arith.cmpi eq, %4, %c0 : index
        scf.if %5 {
          %12 = pod.read %pod_1[@params] : <[@count: index, @comp: !struct.type<@Num2Bits_1::@Num2Bits_1<[]>>, @params: !pod.type<[]>]>, !pod.type<[]>
          %13 = pod.read %pod_2[@in] : <[@in: !felt.type<"goldilocks">]>, !felt.type<"goldilocks">
          %14 = function.call @Num2Bits_1::@Num2Bits_1::@compute(%13) : (!felt.type<"goldilocks">) -> !struct.type<@Num2Bits_1::@Num2Bits_1<[]>> 
          pod.write %pod_1[@comp] = %14 : <[@count: index, @comp: !struct.type<@Num2Bits_1::@Num2Bits_1<[]>>, @params: !pod.type<[]>]>, !struct.type<@Num2Bits_1::@Num2Bits_1<[]>>
        }
        %6 = pod.read %pod_1[@comp] : <[@count: index, @comp: !struct.type<@Num2Bits_1::@Num2Bits_1<[]>>, @params: !pod.type<[]>]>, !struct.type<@Num2Bits_1::@Num2Bits_1<[]>>
        %7 = struct.readm %6[@out] : <@Num2Bits_1::@Num2Bits_1<[]>>, !array.type<33 x !felt.type<"goldilocks">>
        struct.writem %self[@num2bits] = %7 : <@CompConstant_2::@CompConstant_2<[]>>, !array.type<33 x !felt.type<"goldilocks">>
        %felt_const_0_9 = felt.const  0 : <"goldilocks">
        %8 = scf.while (%arg1 = %felt_const_0_9) : (!felt.type<"goldilocks">) -> !felt.type<"goldilocks"> {
          %felt_const_32_10 = felt.const  32 : <"goldilocks">
          %12 = bool.cmp lt(%arg1, %felt_const_32_10) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.condition(%12) %arg1 : !felt.type<"goldilocks">
        } do {
        ^bb0(%arg1: !felt.type<"goldilocks">):
          %felt_const_1_10 = felt.const  1 : <"goldilocks">
          %12 = felt.add %arg1, %felt_const_1_10 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.yield %12 : !felt.type<"goldilocks">
        }
        %felt_const_32 = felt.const  32 : <"goldilocks">
        %9 = cast.toindex %felt_const_32 : !felt.type<"goldilocks">
        %10 = array.read %7[%9] : <33 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
        struct.writem %self[@out] = %10 : <@CompConstant_2::@CompConstant_2<[]>>, !felt.type<"goldilocks">
        struct.writem %self[@Num2Bits_68_1294$inputs] = %pod_2 : <@CompConstant_2::@CompConstant_2<[]>>, !pod.type<[@in: !felt.type<"goldilocks">]>
        %11 = pod.read %pod_1[@comp] : <[@count: index, @comp: !struct.type<@Num2Bits_1::@Num2Bits_1<[]>>, @params: !pod.type<[]>]>, !struct.type<@Num2Bits_1::@Num2Bits_1<[]>>
        struct.writem %self[@Num2Bits_68_1294] = %11 : <@CompConstant_2::@CompConstant_2<[]>>, !struct.type<@Num2Bits_1::@Num2Bits_1<[]>>
        struct.writem %self[@parts] = %nondet_0 : <@CompConstant_2::@CompConstant_2<[]>>, !array.type<32 x !felt.type<"goldilocks">>
        struct.writem %self[@sum] = %nondet : <@CompConstant_2::@CompConstant_2<[]>>, !array.type<32 x !felt.type<"goldilocks">>
        function.return %self : !struct.type<@CompConstant_2::@CompConstant_2<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@CompConstant_2::@CompConstant_2<[]>>, %arg1: !array.type<64 x !felt.type<"goldilocks">> {function.arg_name = "in"}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@out] : <@CompConstant_2::@CompConstant_2<[]>>, !felt.type<"goldilocks">
        %1 = struct.readm %arg0[@parts] : <@CompConstant_2::@CompConstant_2<[]>>, !array.type<32 x !felt.type<"goldilocks">>
        %2 = struct.readm %arg0[@sum] : <@CompConstant_2::@CompConstant_2<[]>>, !array.type<32 x !felt.type<"goldilocks">>
        %3 = struct.readm %arg0[@num2bits] : <@CompConstant_2::@CompConstant_2<[]>>, !array.type<33 x !felt.type<"goldilocks">>
        %4 = struct.readm %arg0[@Num2Bits_68_1294] : <@CompConstant_2::@CompConstant_2<[]>>, !struct.type<@Num2Bits_1::@Num2Bits_1<[]>>
        %5 = struct.readm %arg0[@Num2Bits_68_1294$inputs] : <@CompConstant_2::@CompConstant_2<[]>>, !pod.type<[@in: !felt.type<"goldilocks">]>
        %felt_const_18446744069414584320 = felt.const  18446744069414584320 : <"goldilocks">
        %felt_const_0 = felt.const  0 : <"goldilocks">
        %felt_const_0_0 = felt.const  0 : <"goldilocks">
        %felt_const_0_1 = felt.const  0 : <"goldilocks">
        %felt_const_0_2 = felt.const  0 : <"goldilocks">
        %felt_const_1 = felt.const  1 : <"goldilocks">
        %felt_const_0_3 = felt.const  0 : <"goldilocks">
        %felt_const_0_4 = felt.const  0 : <"goldilocks">
        %6:6 = scf.while (%arg2 = %felt_const_0_1, %arg3 = %felt_const_0_2, %arg4 = %felt_const_0_4, %arg5 = %felt_const_1, %arg6 = %felt_const_0_0, %arg7 = %felt_const_0) : (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">) -> (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">) {
          %felt_const_32_6 = felt.const  32 : <"goldilocks">
          %15 = bool.cmp lt(%arg4, %felt_const_32_6) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.condition(%15) %arg2, %arg3, %arg4, %arg5, %arg6, %arg7 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">
        } do {
        ^bb0(%arg2: !felt.type<"goldilocks">, %arg3: !felt.type<"goldilocks">, %arg4: !felt.type<"goldilocks">, %arg5: !felt.type<"goldilocks">, %arg6: !felt.type<"goldilocks">, %arg7: !felt.type<"goldilocks">):
          %felt_const_18446744069414584320_6 = felt.const  18446744069414584320 : <"goldilocks">
          %felt_const_2 = felt.const  2 : <"goldilocks">
          %15 = felt.mul %arg4, %felt_const_2 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %16 = felt.shr %felt_const_18446744069414584320_6, %15 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_7 = felt.const  1 : <"goldilocks">
          %17 = felt.bit_and %16, %felt_const_1_7 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_18446744069414584320_8 = felt.const  18446744069414584320 : <"goldilocks">
          %felt_const_2_9 = felt.const  2 : <"goldilocks">
          %18 = felt.mul %arg4, %felt_const_2_9 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_10 = felt.const  1 : <"goldilocks">
          %19 = felt.add %18, %felt_const_1_10 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %20 = felt.shr %felt_const_18446744069414584320_8, %19 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_11 = felt.const  1 : <"goldilocks">
          %21 = felt.bit_and %20, %felt_const_1_11 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_2_12 = felt.const  2 : <"goldilocks">
          %22 = felt.mul %arg4, %felt_const_2_12 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %23 = cast.toindex %22 : !felt.type<"goldilocks">
          %24 = array.read %arg1[%23] : <64 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %felt_const_2_13 = felt.const  2 : <"goldilocks">
          %25 = felt.mul %arg4, %felt_const_2_13 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_14 = felt.const  1 : <"goldilocks">
          %26 = felt.add %25, %felt_const_1_14 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %27 = cast.toindex %26 : !felt.type<"goldilocks">
          %28 = array.read %arg1[%27] : <64 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %felt_const_0_15 = felt.const  0 : <"goldilocks">
          %29 = bool.cmp eq(%21, %felt_const_0_15) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_0_16 = felt.const  0 : <"goldilocks">
          %30 = bool.cmp eq(%17, %felt_const_0_16) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %31 = bool.and %29, %30 : i1, i1
          scf.if %31 {
            %35 = felt.mul %28, %arg5 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %36 = felt.mul %24, %arg5 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %37 = felt.add %35, %36 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %38 = felt.mul %28, %24 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %39 = felt.mul %38, %arg5 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %40 = felt.sub %37, %39 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %41 = cast.toindex %arg4 : !felt.type<"goldilocks">
            %42 = array.read %1[%41] : <32 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
            constrain.eq %42, %40 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          } else {
            %35 = felt.mul %arg5, %28 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %36 = felt.mul %35, %24 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %37 = felt.sub %36, %arg5 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %38 = cast.toindex %arg4 : !felt.type<"goldilocks">
            %39 = array.read %1[%38] : <32 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
            constrain.eq %39, %37 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          }
          %felt_const_0_17 = felt.const  0 : <"goldilocks">
          %32 = bool.cmp eq(%arg4, %felt_const_0_17) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.if %32 {
            %felt_const_4294967295 = felt.const  4294967295 : <"goldilocks">
            %felt_const_0_20 = felt.const  0 : <"goldilocks">
            %35 = cast.toindex %felt_const_0_20 : !felt.type<"goldilocks">
            %36 = array.read %1[%35] : <32 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
            %37 = felt.add %felt_const_4294967295, %36 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %felt_const_0_21 = felt.const  0 : <"goldilocks">
            %38 = cast.toindex %felt_const_0_21 : !felt.type<"goldilocks">
            %39 = array.read %2[%38] : <32 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
            constrain.eq %39, %37 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          } else {
            %felt_const_1_20 = felt.const  1 : <"goldilocks">
            %35 = felt.sub %arg4, %felt_const_1_20 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %36 = cast.toindex %35 : !felt.type<"goldilocks">
            %37 = array.read %2[%36] : <32 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
            %38 = cast.toindex %arg4 : !felt.type<"goldilocks">
            %39 = array.read %1[%38] : <32 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
            %40 = felt.add %37, %39 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
            %41 = cast.toindex %arg4 : !felt.type<"goldilocks">
            %42 = array.read %2[%41] : <32 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
            constrain.eq %42, %40 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          }
          %felt_const_2_18 = felt.const  2 : <"goldilocks">
          %33 = felt.mul %arg5, %felt_const_2_18 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1_19 = felt.const  1 : <"goldilocks">
          %34 = felt.add %arg4, %felt_const_1_19 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.yield %24, %28, %34, %33, %21, %17 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">, !felt.type<"goldilocks">
        }
        %felt_const_31 = felt.const  31 : <"goldilocks">
        %7 = cast.toindex %felt_const_31 : !felt.type<"goldilocks">
        %8 = array.read %2[%7] : <32 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
        %9 = pod.read %5[@in] : <[@in: !felt.type<"goldilocks">]>, !felt.type<"goldilocks">
        constrain.eq %9, %8 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        %10 = struct.readm %4[@out] : <@Num2Bits_1::@Num2Bits_1<[]>>, !array.type<33 x !felt.type<"goldilocks">>
        constrain.eq %3, %10 : !array.type<33 x !felt.type<"goldilocks">>, !array.type<33 x !felt.type<"goldilocks">>
        %felt_const_0_5 = felt.const  0 : <"goldilocks">
        %11 = scf.while (%arg2 = %felt_const_0_5) : (!felt.type<"goldilocks">) -> !felt.type<"goldilocks"> {
          %felt_const_32_6 = felt.const  32 : <"goldilocks">
          %15 = bool.cmp lt(%arg2, %felt_const_32_6) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.condition(%15) %arg2 : !felt.type<"goldilocks">
        } do {
        ^bb0(%arg2: !felt.type<"goldilocks">):
          %felt_const_1_6 = felt.const  1 : <"goldilocks">
          %15 = felt.add %arg2, %felt_const_1_6 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.yield %15 : !felt.type<"goldilocks">
        }
        %felt_const_32 = felt.const  32 : <"goldilocks">
        %12 = cast.toindex %felt_const_32 : !felt.type<"goldilocks">
        %13 = array.read %3[%12] : <33 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
        constrain.eq %0, %13 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        %14 = pod.read %5[@in] : <[@in: !felt.type<"goldilocks">]>, !felt.type<"goldilocks">
        function.call @Num2Bits_1::@Num2Bits_1::@constrain(%4, %14) : (!struct.type<@Num2Bits_1::@Num2Bits_1<[]>>, !felt.type<"goldilocks">) -> () 
        function.return
      }
    }
  }
  poly.template @AliasCheck_3 {
    struct.def @AliasCheck_3 {
      struct.member @compConstant : !felt.type<"goldilocks">
      struct.member @CompConstant_81_1495 : !struct.type<@CompConstant_2::@CompConstant_2<[]>>
      struct.member @CompConstant_81_1495$inputs : !pod.type<[@in: !array.type<64 x !felt.type<"goldilocks">>]>
      function.def @compute(%arg0: !array.type<64 x !felt.type<"goldilocks">> {function.arg_name = "in"}) -> !struct.type<@AliasCheck_3::@AliasCheck_3<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@AliasCheck_3::@AliasCheck_3<[]>>
        %pod = pod.new : <[]>
        %c64 = arith.constant 64 : index
        %pod_0 = pod.new { @count = %c64, @params = %pod }  : <[@count: index, @comp: !struct.type<@CompConstant_2::@CompConstant_2<[]>>, @params: !pod.type<[]>]>
        %pod_1 = pod.new : <[@in: !array.type<64 x !felt.type<"goldilocks">>]>
        pod.write %pod_1[@in] = %arg0 : <[@in: !array.type<64 x !felt.type<"goldilocks">>]>, !array.type<64 x !felt.type<"goldilocks">>
        %0 = pod.read %pod_0[@count] : <[@count: index, @comp: !struct.type<@CompConstant_2::@CompConstant_2<[]>>, @params: !pod.type<[]>]>, index
        %c1 = arith.constant 1 : index
        %1 = arith.subi %0, %c1 : index
        pod.write %pod_0[@count] = %1 : <[@count: index, @comp: !struct.type<@CompConstant_2::@CompConstant_2<[]>>, @params: !pod.type<[]>]>, index
        %c0 = arith.constant 0 : index
        %2 = arith.cmpi eq, %1, %c0 : index
        scf.if %2 {
          %6 = pod.read %pod_0[@params] : <[@count: index, @comp: !struct.type<@CompConstant_2::@CompConstant_2<[]>>, @params: !pod.type<[]>]>, !pod.type<[]>
          %7 = pod.read %pod_1[@in] : <[@in: !array.type<64 x !felt.type<"goldilocks">>]>, !array.type<64 x !felt.type<"goldilocks">>
          %8 = function.call @CompConstant_2::@CompConstant_2::@compute(%7) : (!array.type<64 x !felt.type<"goldilocks">>) -> !struct.type<@CompConstant_2::@CompConstant_2<[]>> 
          pod.write %pod_0[@comp] = %8 : <[@count: index, @comp: !struct.type<@CompConstant_2::@CompConstant_2<[]>>, @params: !pod.type<[]>]>, !struct.type<@CompConstant_2::@CompConstant_2<[]>>
        }
        %3 = pod.read %pod_0[@comp] : <[@count: index, @comp: !struct.type<@CompConstant_2::@CompConstant_2<[]>>, @params: !pod.type<[]>]>, !struct.type<@CompConstant_2::@CompConstant_2<[]>>
        %4 = struct.readm %3[@out] : <@CompConstant_2::@CompConstant_2<[]>>, !felt.type<"goldilocks">
        struct.writem %self[@compConstant] = %4 : <@AliasCheck_3::@AliasCheck_3<[]>>, !felt.type<"goldilocks">
        struct.writem %self[@CompConstant_81_1495$inputs] = %pod_1 : <@AliasCheck_3::@AliasCheck_3<[]>>, !pod.type<[@in: !array.type<64 x !felt.type<"goldilocks">>]>
        %5 = pod.read %pod_0[@comp] : <[@count: index, @comp: !struct.type<@CompConstant_2::@CompConstant_2<[]>>, @params: !pod.type<[]>]>, !struct.type<@CompConstant_2::@CompConstant_2<[]>>
        struct.writem %self[@CompConstant_81_1495] = %5 : <@AliasCheck_3::@AliasCheck_3<[]>>, !struct.type<@CompConstant_2::@CompConstant_2<[]>>
        function.return %self : !struct.type<@AliasCheck_3::@AliasCheck_3<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@AliasCheck_3::@AliasCheck_3<[]>>, %arg1: !array.type<64 x !felt.type<"goldilocks">> {function.arg_name = "in"}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@compConstant] : <@AliasCheck_3::@AliasCheck_3<[]>>, !felt.type<"goldilocks">
        %1 = struct.readm %arg0[@CompConstant_81_1495] : <@AliasCheck_3::@AliasCheck_3<[]>>, !struct.type<@CompConstant_2::@CompConstant_2<[]>>
        %2 = struct.readm %arg0[@CompConstant_81_1495$inputs] : <@AliasCheck_3::@AliasCheck_3<[]>>, !pod.type<[@in: !array.type<64 x !felt.type<"goldilocks">>]>
        %3 = pod.read %2[@in] : <[@in: !array.type<64 x !felt.type<"goldilocks">>]>, !array.type<64 x !felt.type<"goldilocks">>
        constrain.eq %3, %arg1 : !array.type<64 x !felt.type<"goldilocks">>, !array.type<64 x !felt.type<"goldilocks">>
        %4 = struct.readm %1[@out] : <@CompConstant_2::@CompConstant_2<[]>>, !felt.type<"goldilocks">
        constrain.eq %0, %4 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        %felt_const_0 = felt.const  0 : <"goldilocks">
        constrain.eq %0, %felt_const_0 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        %5 = pod.read %2[@in] : <[@in: !array.type<64 x !felt.type<"goldilocks">>]>, !array.type<64 x !felt.type<"goldilocks">>
        function.call @CompConstant_2::@CompConstant_2::@constrain(%1, %5) : (!struct.type<@CompConstant_2::@CompConstant_2<[]>>, !array.type<64 x !felt.type<"goldilocks">>) -> () 
        function.return
      }
    }
  }
  poly.template @Num2Bits_strict_4 {
    struct.def @Num2Bits_strict_4 {
      struct.member @out : !array.type<64 x !felt.type<"goldilocks">> {llzk.pub}
      struct.member @n2b : !array.type<64 x !felt.type<"goldilocks">>
      struct.member @AliasCheck_91_1681 : !struct.type<@AliasCheck_3::@AliasCheck_3<[]>>
      struct.member @AliasCheck_91_1681$inputs : !pod.type<[@in: !array.type<64 x !felt.type<"goldilocks">>]>
      struct.member @Num2Bits_89_1654 : !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
      struct.member @Num2Bits_89_1654$inputs : !pod.type<[@in: !felt.type<"goldilocks">]>
      function.def @compute(%arg0: !felt.type<"goldilocks"> {function.arg_name = "in"}) -> !struct.type<@Num2Bits_strict_4::@Num2Bits_strict_4<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>
        %pod = pod.new : <[]>
        %c64 = arith.constant 64 : index
        %pod_0 = pod.new { @count = %c64, @params = %pod }  : <[@count: index, @comp: !struct.type<@AliasCheck_3::@AliasCheck_3<[]>>, @params: !pod.type<[]>]>
        %pod_1 = pod.new : <[@in: !array.type<64 x !felt.type<"goldilocks">>]>
        %pod_2 = pod.new : <[]>
        %c1 = arith.constant 1 : index
        %pod_3 = pod.new { @count = %c1, @params = %pod_2 }  : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>
        %pod_4 = pod.new : <[@in: !felt.type<"goldilocks">]>
        pod.write %pod_4[@in] = %arg0 : <[@in: !felt.type<"goldilocks">]>, !felt.type<"goldilocks">
        %0 = pod.read %pod_3[@count] : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>, index
        %c1_5 = arith.constant 1 : index
        %1 = arith.subi %0, %c1_5 : index
        pod.write %pod_3[@count] = %1 : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>, index
        %c0 = arith.constant 0 : index
        %2 = arith.cmpi eq, %1, %c0 : index
        scf.if %2 {
          %10 = pod.read %pod_3[@params] : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>, !pod.type<[]>
          %11 = pod.read %pod_4[@in] : <[@in: !felt.type<"goldilocks">]>, !felt.type<"goldilocks">
          %12 = function.call @Num2Bits_0::@Num2Bits_0::@compute(%11) : (!felt.type<"goldilocks">) -> !struct.type<@Num2Bits_0::@Num2Bits_0<[]>> 
          pod.write %pod_3[@comp] = %12 : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>, !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
        }
        %3 = pod.read %pod_3[@comp] : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>, !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
        %4 = struct.readm %3[@out] : <@Num2Bits_0::@Num2Bits_0<[]>>, !array.type<64 x !felt.type<"goldilocks">>
        struct.writem %self[@n2b] = %4 : <@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, !array.type<64 x !felt.type<"goldilocks">>
        pod.write %pod_1[@in] = %4 : <[@in: !array.type<64 x !felt.type<"goldilocks">>]>, !array.type<64 x !felt.type<"goldilocks">>
        %5 = pod.read %pod_0[@count] : <[@count: index, @comp: !struct.type<@AliasCheck_3::@AliasCheck_3<[]>>, @params: !pod.type<[]>]>, index
        %c1_6 = arith.constant 1 : index
        %6 = arith.subi %5, %c1_6 : index
        pod.write %pod_0[@count] = %6 : <[@count: index, @comp: !struct.type<@AliasCheck_3::@AliasCheck_3<[]>>, @params: !pod.type<[]>]>, index
        %c0_7 = arith.constant 0 : index
        %7 = arith.cmpi eq, %6, %c0_7 : index
        scf.if %7 {
          %10 = pod.read %pod_0[@params] : <[@count: index, @comp: !struct.type<@AliasCheck_3::@AliasCheck_3<[]>>, @params: !pod.type<[]>]>, !pod.type<[]>
          %11 = pod.read %pod_1[@in] : <[@in: !array.type<64 x !felt.type<"goldilocks">>]>, !array.type<64 x !felt.type<"goldilocks">>
          %12 = function.call @AliasCheck_3::@AliasCheck_3::@compute(%11) : (!array.type<64 x !felt.type<"goldilocks">>) -> !struct.type<@AliasCheck_3::@AliasCheck_3<[]>> 
          pod.write %pod_0[@comp] = %12 : <[@count: index, @comp: !struct.type<@AliasCheck_3::@AliasCheck_3<[]>>, @params: !pod.type<[]>]>, !struct.type<@AliasCheck_3::@AliasCheck_3<[]>>
        }
        struct.writem %self[@out] = %4 : <@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, !array.type<64 x !felt.type<"goldilocks">>
        struct.writem %self[@Num2Bits_89_1654$inputs] = %pod_4 : <@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, !pod.type<[@in: !felt.type<"goldilocks">]>
        %8 = pod.read %pod_3[@comp] : <[@count: index, @comp: !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, @params: !pod.type<[]>]>, !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
        struct.writem %self[@Num2Bits_89_1654] = %8 : <@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
        struct.writem %self[@AliasCheck_91_1681$inputs] = %pod_1 : <@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, !pod.type<[@in: !array.type<64 x !felt.type<"goldilocks">>]>
        %9 = pod.read %pod_0[@comp] : <[@count: index, @comp: !struct.type<@AliasCheck_3::@AliasCheck_3<[]>>, @params: !pod.type<[]>]>, !struct.type<@AliasCheck_3::@AliasCheck_3<[]>>
        struct.writem %self[@AliasCheck_91_1681] = %9 : <@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, !struct.type<@AliasCheck_3::@AliasCheck_3<[]>>
        function.return %self : !struct.type<@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, %arg1: !felt.type<"goldilocks"> {function.arg_name = "in"}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@out] : <@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, !array.type<64 x !felt.type<"goldilocks">>
        %1 = struct.readm %arg0[@n2b] : <@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, !array.type<64 x !felt.type<"goldilocks">>
        %2 = struct.readm %arg0[@AliasCheck_91_1681] : <@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, !struct.type<@AliasCheck_3::@AliasCheck_3<[]>>
        %3 = struct.readm %arg0[@AliasCheck_91_1681$inputs] : <@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, !pod.type<[@in: !array.type<64 x !felt.type<"goldilocks">>]>
        %4 = struct.readm %arg0[@Num2Bits_89_1654] : <@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, !struct.type<@Num2Bits_0::@Num2Bits_0<[]>>
        %5 = struct.readm %arg0[@Num2Bits_89_1654$inputs] : <@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, !pod.type<[@in: !felt.type<"goldilocks">]>
        %6 = pod.read %5[@in] : <[@in: !felt.type<"goldilocks">]>, !felt.type<"goldilocks">
        constrain.eq %6, %arg1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        %7 = struct.readm %4[@out] : <@Num2Bits_0::@Num2Bits_0<[]>>, !array.type<64 x !felt.type<"goldilocks">>
        constrain.eq %1, %7 : !array.type<64 x !felt.type<"goldilocks">>, !array.type<64 x !felt.type<"goldilocks">>
        %8 = pod.read %3[@in] : <[@in: !array.type<64 x !felt.type<"goldilocks">>]>, !array.type<64 x !felt.type<"goldilocks">>
        constrain.eq %8, %1 : !array.type<64 x !felt.type<"goldilocks">>, !array.type<64 x !felt.type<"goldilocks">>
        constrain.eq %0, %1 : !array.type<64 x !felt.type<"goldilocks">>, !array.type<64 x !felt.type<"goldilocks">>
        %9 = pod.read %5[@in] : <[@in: !felt.type<"goldilocks">]>, !felt.type<"goldilocks">
        function.call @Num2Bits_0::@Num2Bits_0::@constrain(%4, %9) : (!struct.type<@Num2Bits_0::@Num2Bits_0<[]>>, !felt.type<"goldilocks">) -> () 
        %10 = pod.read %3[@in] : <[@in: !array.type<64 x !felt.type<"goldilocks">>]>, !array.type<64 x !felt.type<"goldilocks">>
        function.call @AliasCheck_3::@AliasCheck_3::@constrain(%2, %10) : (!struct.type<@AliasCheck_3::@AliasCheck_3<[]>>, !array.type<64 x !felt.type<"goldilocks">>) -> () 
        function.return
      }
    }
  }
  poly.template @SignFp_5 {
    struct.def @SignFp_5 {
      struct.member @sign : !felt.type<"goldilocks"> {llzk.pub}
      struct.member @a_bits : !array.type<64 x !felt.type<"goldilocks">>
      struct.member @Num2Bits_strict_5_100 : !struct.type<@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>
      struct.member @Num2Bits_strict_5_100$inputs : !pod.type<[@in: !felt.type<"goldilocks">]>
      function.def @compute(%arg0: !felt.type<"goldilocks"> {function.arg_name = "a"}) -> !struct.type<@SignFp_5::@SignFp_5<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@SignFp_5::@SignFp_5<[]>>
        %pod = pod.new : <[]>
        %c1 = arith.constant 1 : index
        %pod_0 = pod.new { @count = %c1, @params = %pod }  : <[@count: index, @comp: !struct.type<@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, @params: !pod.type<[]>]>
        %pod_1 = pod.new : <[@in: !felt.type<"goldilocks">]>
        pod.write %pod_1[@in] = %arg0 : <[@in: !felt.type<"goldilocks">]>, !felt.type<"goldilocks">
        %0 = pod.read %pod_0[@count] : <[@count: index, @comp: !struct.type<@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, @params: !pod.type<[]>]>, index
        %c1_2 = arith.constant 1 : index
        %1 = arith.subi %0, %c1_2 : index
        pod.write %pod_0[@count] = %1 : <[@count: index, @comp: !struct.type<@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, @params: !pod.type<[]>]>, index
        %c0 = arith.constant 0 : index
        %2 = arith.cmpi eq, %1, %c0 : index
        scf.if %2 {
          %8 = pod.read %pod_0[@params] : <[@count: index, @comp: !struct.type<@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, @params: !pod.type<[]>]>, !pod.type<[]>
          %9 = pod.read %pod_1[@in] : <[@in: !felt.type<"goldilocks">]>, !felt.type<"goldilocks">
          %10 = function.call @Num2Bits_strict_4::@Num2Bits_strict_4::@compute(%9) : (!felt.type<"goldilocks">) -> !struct.type<@Num2Bits_strict_4::@Num2Bits_strict_4<[]>> 
          pod.write %pod_0[@comp] = %10 : <[@count: index, @comp: !struct.type<@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, @params: !pod.type<[]>]>, !struct.type<@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>
        }
        %3 = pod.read %pod_0[@comp] : <[@count: index, @comp: !struct.type<@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, @params: !pod.type<[]>]>, !struct.type<@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>
        %4 = struct.readm %3[@out] : <@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, !array.type<64 x !felt.type<"goldilocks">>
        struct.writem %self[@a_bits] = %4 : <@SignFp_5::@SignFp_5<[]>>, !array.type<64 x !felt.type<"goldilocks">>
        %felt_const_0 = felt.const  0 : <"goldilocks">
        %5 = cast.toindex %felt_const_0 : !felt.type<"goldilocks">
        %6 = array.read %4[%5] : <64 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
        struct.writem %self[@sign] = %6 : <@SignFp_5::@SignFp_5<[]>>, !felt.type<"goldilocks">
        struct.writem %self[@Num2Bits_strict_5_100$inputs] = %pod_1 : <@SignFp_5::@SignFp_5<[]>>, !pod.type<[@in: !felt.type<"goldilocks">]>
        %7 = pod.read %pod_0[@comp] : <[@count: index, @comp: !struct.type<@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, @params: !pod.type<[]>]>, !struct.type<@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>
        struct.writem %self[@Num2Bits_strict_5_100] = %7 : <@SignFp_5::@SignFp_5<[]>>, !struct.type<@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>
        function.return %self : !struct.type<@SignFp_5::@SignFp_5<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@SignFp_5::@SignFp_5<[]>>, %arg1: !felt.type<"goldilocks"> {function.arg_name = "a"}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@sign] : <@SignFp_5::@SignFp_5<[]>>, !felt.type<"goldilocks">
        %1 = struct.readm %arg0[@a_bits] : <@SignFp_5::@SignFp_5<[]>>, !array.type<64 x !felt.type<"goldilocks">>
        %2 = struct.readm %arg0[@Num2Bits_strict_5_100] : <@SignFp_5::@SignFp_5<[]>>, !struct.type<@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>
        %3 = struct.readm %arg0[@Num2Bits_strict_5_100$inputs] : <@SignFp_5::@SignFp_5<[]>>, !pod.type<[@in: !felt.type<"goldilocks">]>
        %4 = pod.read %3[@in] : <[@in: !felt.type<"goldilocks">]>, !felt.type<"goldilocks">
        constrain.eq %4, %arg1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        %5 = struct.readm %2[@out] : <@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, !array.type<64 x !felt.type<"goldilocks">>
        constrain.eq %1, %5 : !array.type<64 x !felt.type<"goldilocks">>, !array.type<64 x !felt.type<"goldilocks">>
        %felt_const_0 = felt.const  0 : <"goldilocks">
        %6 = cast.toindex %felt_const_0 : !felt.type<"goldilocks">
        %7 = array.read %1[%6] : <64 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
        constrain.eq %0, %7 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        %8 = pod.read %3[@in] : <[@in: !felt.type<"goldilocks">]>, !felt.type<"goldilocks">
        function.call @Num2Bits_strict_4::@Num2Bits_strict_4::@constrain(%2, %8) : (!struct.type<@Num2Bits_strict_4::@Num2Bits_strict_4<[]>>, !felt.type<"goldilocks">) -> () 
        function.return
      }
    }
  }
}
