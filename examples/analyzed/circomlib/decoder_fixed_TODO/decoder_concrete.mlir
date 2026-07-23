module attributes {llzk.lang = "circom", llzk.main = !struct.type<@Decoder_1::@Decoder_1<[]>>} {
  poly.template @IsZero_0 {
    struct.def @IsZero_0 {
      struct.member @out : !felt.type<"goldilocks"> {llzk.pub}
      struct.member @inv : !felt.type<"goldilocks">
      function.def @compute(%arg0: !felt.type<"goldilocks"> {function.arg_name = "in"}) -> !struct.type<@IsZero_0::@IsZero_0<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@IsZero_0::@IsZero_0<[]>>
        %felt_const_0 = felt.const  0 : <"goldilocks">
        %0 = bool.cmp ne(%arg0, %felt_const_0) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        %1 = scf.if %0 -> (!felt.type<"goldilocks">) {
          %felt_const_1_0 = felt.const  1 : <"goldilocks">
          %5 = felt.div %felt_const_1_0, %arg0 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          struct.writem %self[@inv] = %5 : <@IsZero_0::@IsZero_0<[]>>, !felt.type<"goldilocks">
          scf.yield %5 : !felt.type<"goldilocks">
        } else {
          %felt_const_0_0 = felt.const  0 : <"goldilocks">
          struct.writem %self[@inv] = %felt_const_0_0 : <@IsZero_0::@IsZero_0<[]>>, !felt.type<"goldilocks">
          scf.yield %felt_const_0_0 : !felt.type<"goldilocks">
        }
        %2 = felt.neg %arg0 : !felt.type<"goldilocks">
        %3 = felt.mul %2, %1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        %felt_const_1 = felt.const  1 : <"goldilocks">
        %4 = felt.add %3, %felt_const_1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        struct.writem %self[@out] = %4 : <@IsZero_0::@IsZero_0<[]>>, !felt.type<"goldilocks">
        function.return %self : !struct.type<@IsZero_0::@IsZero_0<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@IsZero_0::@IsZero_0<[]>>, %arg1: !felt.type<"goldilocks"> {function.arg_name = "in"}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@out] : <@IsZero_0::@IsZero_0<[]>>, !felt.type<"goldilocks">
        %1 = struct.readm %arg0[@inv] : <@IsZero_0::@IsZero_0<[]>>, !felt.type<"goldilocks">
        %felt_const_0 = felt.const  0 : <"goldilocks">
        %2 = bool.cmp ne(%arg1, %felt_const_0) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        scf.if %2 {
        } else {
        }
        %3 = felt.neg %arg1 : !felt.type<"goldilocks">
        %4 = felt.mul %3, %1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        %felt_const_1 = felt.const  1 : <"goldilocks">
        %5 = felt.add %4, %felt_const_1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        constrain.eq %0, %5 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        %6 = felt.mul %arg1, %0 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        %felt_const_0_0 = felt.const  0 : <"goldilocks">
        constrain.eq %6, %felt_const_0_0 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        function.return
      }
    }
  }
  poly.template @Decoder_1 {
    struct.def @Decoder_1 {
      struct.member @out : !array.type<4 x !felt.type<"goldilocks">> {llzk.pub}
      struct.member @success : !felt.type<"goldilocks"> {llzk.pub}
      struct.member @checkZero : !array.type<4 x !struct.type<@IsZero_0::@IsZero_0<[]>>>
      struct.member @checkZero$inputs : !array.type<4 x !pod.type<[@in: !felt.type<"goldilocks">]>>
      function.def @compute(%arg0: !felt.type<"goldilocks"> {function.arg_name = "inp"}) -> !struct.type<@Decoder_1::@Decoder_1<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@Decoder_1::@Decoder_1<[]>>
        %nondet = llzk.nondet : !array.type<4 x !felt.type<"goldilocks">>
        %array = array.new  : <4 x !pod.type<[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>> 
        %pod = pod.new : <[]>
        %c4 = arith.constant 4 : index
        %c0 = arith.constant 0 : index
        %c1 = arith.constant 1 : index
        scf.for %arg1 = %c0 to %c4 step %c1 {
          %c1_6 = arith.constant 1 : index
          %pod_7 = pod.new { @count = %c1_6, @params = %pod }  : <[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>
          array.write %array[%arg1] = %pod_7 : <4 x !pod.type<[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>>, !pod.type<[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>
        }
        %array_0 = array.new  : <4 x !pod.type<[@in: !felt.type<"goldilocks">]>> 
        %felt_const_4 = felt.const  4 : <"goldilocks">
        %felt_const_0 = felt.const  0 : <"goldilocks">
        %felt_const_0_1 = felt.const  0 : <"goldilocks">
        %0:3 = scf.while (%arg1 = %felt_const_0_1, %arg2 = %felt_const_0, %arg3 = %array_0) : (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !array.type<4 x !pod.type<[@in: !felt.type<"goldilocks">]>>) -> (!felt.type<"goldilocks">, !felt.type<"goldilocks">, !array.type<4 x !pod.type<[@in: !felt.type<"goldilocks">]>>) {
          %felt_const_4_6 = felt.const  4 : <"goldilocks">
          %1 = bool.cmp lt(%arg1, %felt_const_4_6) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.condition(%1) %arg1, %arg2, %arg3 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !array.type<4 x !pod.type<[@in: !felt.type<"goldilocks">]>>
        } do {
        ^bb0(%arg1: !felt.type<"goldilocks">, %arg2: !felt.type<"goldilocks">, %arg3: !array.type<4 x !pod.type<[@in: !felt.type<"goldilocks">]>>):
          %1 = felt.sub %arg0, %arg1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %2 = cast.toindex %arg1 : !felt.type<"goldilocks">
          %3 = array.read %arg3[%2] : <4 x !pod.type<[@in: !felt.type<"goldilocks">]>>, !pod.type<[@in: !felt.type<"goldilocks">]>
          pod.write %3[@in] = %1 : <[@in: !felt.type<"goldilocks">]>, !felt.type<"goldilocks">
          %4 = cast.toindex %arg1 : !felt.type<"goldilocks">
          array.write %arg3[%4] = %3 : <4 x !pod.type<[@in: !felt.type<"goldilocks">]>>, !pod.type<[@in: !felt.type<"goldilocks">]>
          %5 = cast.toindex %arg1 : !felt.type<"goldilocks">
          %6 = array.read %array[%5] : <4 x !pod.type<[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>>, !pod.type<[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>
          %7 = cast.toindex %arg1 : !felt.type<"goldilocks">
          %8 = array.read %arg3[%7] : <4 x !pod.type<[@in: !felt.type<"goldilocks">]>>, !pod.type<[@in: !felt.type<"goldilocks">]>
          %9 = pod.read %6[@count] : <[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>, index
          %c1_6 = arith.constant 1 : index
          %10 = arith.subi %9, %c1_6 : index
          pod.write %6[@count] = %10 : <[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>, index
          %c0_7 = arith.constant 0 : index
          %11 = arith.cmpi eq, %10, %c0_7 : index
          scf.if %11 {
            %21 = pod.read %6[@params] : <[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>, !pod.type<[]>
            %22 = pod.read %8[@in] : <[@in: !felt.type<"goldilocks">]>, !felt.type<"goldilocks">
            %23 = function.call @IsZero_0::@IsZero_0::@compute(%22) : (!felt.type<"goldilocks">) -> !struct.type<@IsZero_0::@IsZero_0<[]>> 
            pod.write %6[@comp] = %23 : <[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsZero_0::@IsZero_0<[]>>
            %24 = cast.toindex %arg1 : !felt.type<"goldilocks">
            array.write %array[%24] = %6 : <4 x !pod.type<[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>>, !pod.type<[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>
          }
          %12 = cast.toindex %arg1 : !felt.type<"goldilocks">
          %13 = array.read %array[%12] : <4 x !pod.type<[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>>, !pod.type<[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>
          %14 = pod.read %13[@comp] : <[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsZero_0::@IsZero_0<[]>>
          %15 = struct.readm %14[@out] : <@IsZero_0::@IsZero_0<[]>>, !felt.type<"goldilocks">
          %16 = cast.toindex %arg1 : !felt.type<"goldilocks">
          array.write %nondet[%16] = %15 : <4 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %17 = cast.toindex %arg1 : !felt.type<"goldilocks">
          %18 = array.read %nondet[%17] : <4 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %19 = felt.add %arg2, %18 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1 = felt.const  1 : <"goldilocks">
          %20 = felt.add %arg1, %felt_const_1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.yield %20, %19, %arg3 : !felt.type<"goldilocks">, !felt.type<"goldilocks">, !array.type<4 x !pod.type<[@in: !felt.type<"goldilocks">]>>
        }
        struct.writem %self[@success] = %0#1 : <@Decoder_1::@Decoder_1<[]>>, !felt.type<"goldilocks">
        struct.writem %self[@checkZero$inputs] = %0#2 : <@Decoder_1::@Decoder_1<[]>>, !array.type<4 x !pod.type<[@in: !felt.type<"goldilocks">]>>
        %array_2 = array.new  : <4 x !struct.type<@IsZero_0::@IsZero_0<[]>>> 
        %c4_3 = arith.constant 4 : index
        %c0_4 = arith.constant 0 : index
        %c1_5 = arith.constant 1 : index
        scf.for %arg1 = %c0_4 to %c4_3 step %c1_5 {
          %1 = array.read %array[%arg1] : <4 x !pod.type<[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>>, !pod.type<[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>
          %2 = pod.read %1[@comp] : <[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsZero_0::@IsZero_0<[]>>
          array.write %array_2[%arg1] = %2 : <4 x !struct.type<@IsZero_0::@IsZero_0<[]>>>, !struct.type<@IsZero_0::@IsZero_0<[]>>
        }
        struct.writem %self[@checkZero] = %array_2 : <@Decoder_1::@Decoder_1<[]>>, !array.type<4 x !struct.type<@IsZero_0::@IsZero_0<[]>>>
        struct.writem %self[@out] = %nondet : <@Decoder_1::@Decoder_1<[]>>, !array.type<4 x !felt.type<"goldilocks">>
        function.return %self : !struct.type<@Decoder_1::@Decoder_1<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@Decoder_1::@Decoder_1<[]>>, %arg1: !felt.type<"goldilocks"> {function.arg_name = "inp"}) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@out] : <@Decoder_1::@Decoder_1<[]>>, !array.type<4 x !felt.type<"goldilocks">>
        %1 = struct.readm %arg0[@success] : <@Decoder_1::@Decoder_1<[]>>, !felt.type<"goldilocks">
        %2 = struct.readm %arg0[@checkZero] : <@Decoder_1::@Decoder_1<[]>>, !array.type<4 x !struct.type<@IsZero_0::@IsZero_0<[]>>>
        %3 = struct.readm %arg0[@checkZero$inputs] : <@Decoder_1::@Decoder_1<[]>>, !array.type<4 x !pod.type<[@in: !felt.type<"goldilocks">]>>
        %felt_const_4 = felt.const  4 : <"goldilocks">
        %felt_const_0 = felt.const  0 : <"goldilocks">
        %felt_const_0_0 = felt.const  0 : <"goldilocks">
        %4:2 = scf.while (%arg2 = %felt_const_0, %arg3 = %felt_const_0_0) : (!felt.type<"goldilocks">, !felt.type<"goldilocks">) -> (!felt.type<"goldilocks">, !felt.type<"goldilocks">) {
          %felt_const_4_1 = felt.const  4 : <"goldilocks">
          %5 = bool.cmp lt(%arg3, %felt_const_4_1) : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.condition(%5) %arg2, %arg3 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        } do {
        ^bb0(%arg2: !felt.type<"goldilocks">, %arg3: !felt.type<"goldilocks">):
          %5 = felt.sub %arg1, %arg3 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %6 = cast.toindex %arg3 : !felt.type<"goldilocks">
          %7 = array.read %3[%6] : <4 x !pod.type<[@in: !felt.type<"goldilocks">]>>, !pod.type<[@in: !felt.type<"goldilocks">]>
          %8 = pod.read %7[@in] : <[@in: !felt.type<"goldilocks">]>, !felt.type<"goldilocks">
          constrain.eq %8, %5 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %9 = cast.toindex %arg3 : !felt.type<"goldilocks">
          %10 = array.read %2[%9] : <4 x !struct.type<@IsZero_0::@IsZero_0<[]>>>, !struct.type<@IsZero_0::@IsZero_0<[]>>
          %11 = struct.readm %10[@out] : <@IsZero_0::@IsZero_0<[]>>, !felt.type<"goldilocks">
          %12 = cast.toindex %arg3 : !felt.type<"goldilocks">
          %13 = array.read %0[%12] : <4 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          constrain.eq %13, %11 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %14 = cast.toindex %arg3 : !felt.type<"goldilocks">
          %15 = array.read %0[%14] : <4 x !felt.type<"goldilocks">>, !felt.type<"goldilocks">
          %16 = felt.add %arg2, %15 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          %felt_const_1 = felt.const  1 : <"goldilocks">
          %17 = felt.add %arg3, %felt_const_1 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
          scf.yield %16, %17 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        }
        constrain.eq %1, %4#0 : !felt.type<"goldilocks">, !felt.type<"goldilocks">
        %c4 = arith.constant 4 : index
        %c0 = arith.constant 0 : index
        %c1 = arith.constant 1 : index
        scf.for %arg2 = %c0 to %c4 step %c1 {
          %5 = array.read %2[%arg2] : <4 x !struct.type<@IsZero_0::@IsZero_0<[]>>>, !struct.type<@IsZero_0::@IsZero_0<[]>>
          %6 = array.read %3[%arg2] : <4 x !pod.type<[@in: !felt.type<"goldilocks">]>>, !pod.type<[@in: !felt.type<"goldilocks">]>
          %7 = pod.read %6[@in] : <[@in: !felt.type<"goldilocks">]>, !felt.type<"goldilocks">
          function.call @IsZero_0::@IsZero_0::@constrain(%5, %7) : (!struct.type<@IsZero_0::@IsZero_0<[]>>, !felt.type<"goldilocks">) -> () 
        }
        function.return
      }
    }
  }
}
