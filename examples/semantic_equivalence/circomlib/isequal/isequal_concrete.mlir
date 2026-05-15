module attributes {llzk.lang, llzk.main = !struct.type<@IsEqual_1::@IsEqual_1<[]>>} {
  poly.template @IsZero_0 {
    struct.def @IsZero_0 {
      struct.member @out : !felt.type<"bn128"> {llzk.pub}
      struct.member @inv : !felt.type<"bn128">
      function.def @compute(%arg0: !felt.type<"bn128">) -> !struct.type<@IsZero_0::@IsZero_0<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@IsZero_0::@IsZero_0<[]>>
        %felt_const_0 = felt.const  0 : <"bn128">
        %0 = bool.cmp ne(%arg0, %felt_const_0) : !felt.type<"bn128">, !felt.type<"bn128">
        %1 = scf.if %0 -> (!felt.type<"bn128">) {
          %felt_const_1_0 = felt.const  1 : <"bn128">
          %5 = felt.div %felt_const_1_0, %arg0 : !felt.type<"bn128">, !felt.type<"bn128">
          struct.writem %self[@inv] = %5 : <@IsZero_0::@IsZero_0<[]>>, !felt.type<"bn128">
          scf.yield %5 : !felt.type<"bn128">
        } else {
          %felt_const_0_0 = felt.const  0 : <"bn128">
          struct.writem %self[@inv] = %felt_const_0_0 : <@IsZero_0::@IsZero_0<[]>>, !felt.type<"bn128">
          scf.yield %felt_const_0_0 : !felt.type<"bn128">
        }
        %2 = felt.neg %arg0 : !felt.type<"bn128">
        %3 = felt.mul %2, %1 : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_1 = felt.const  1 : <"bn128">
        %4 = felt.add %3, %felt_const_1 : !felt.type<"bn128">, !felt.type<"bn128">
        struct.writem %self[@out] = %4 : <@IsZero_0::@IsZero_0<[]>>, !felt.type<"bn128">
        function.return %self : !struct.type<@IsZero_0::@IsZero_0<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@IsZero_0::@IsZero_0<[]>>, %arg1: !felt.type<"bn128">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@out] : <@IsZero_0::@IsZero_0<[]>>, !felt.type<"bn128">
        %1 = struct.readm %arg0[@inv] : <@IsZero_0::@IsZero_0<[]>>, !felt.type<"bn128">
        %felt_const_0 = felt.const  0 : <"bn128">
        %2 = bool.cmp ne(%arg1, %felt_const_0) : !felt.type<"bn128">, !felt.type<"bn128">
        scf.if %2 {
        } else {
        }
        %3 = felt.neg %arg1 : !felt.type<"bn128">
        %4 = felt.mul %3, %1 : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_1 = felt.const  1 : <"bn128">
        %5 = felt.add %4, %felt_const_1 : !felt.type<"bn128">, !felt.type<"bn128">
        constrain.eq %0, %5 : !felt.type<"bn128">, !felt.type<"bn128">
        %6 = felt.mul %arg1, %0 : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_0_0 = felt.const  0 : <"bn128">
        constrain.eq %6, %felt_const_0_0 : !felt.type<"bn128">, !felt.type<"bn128">
        function.return
      }
    }
  }
  poly.template @IsEqual_1 {
    struct.def @IsEqual_1 {
      struct.member @out : !felt.type<"bn128"> {llzk.pub}
      struct.member @isz : !struct.type<@IsZero_0::@IsZero_0<[]>>
      struct.member @isz$inputs : !pod.type<[@in: !felt.type<"bn128">]>
      function.def @compute(%arg0: !array.type<2 x !felt.type<"bn128">>) -> !struct.type<@IsEqual_1::@IsEqual_1<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@IsEqual_1::@IsEqual_1<[]>>
        %c1 = arith.constant 1 : index
        %pod = pod.new { @count = %c1 }  : <[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>
        %pod_0 = pod.new : <[@in: !felt.type<"bn128">]>
        %felt_const_1 = felt.const  1 : <"bn128">
        %0 = cast.toindex %felt_const_1 : !felt.type<"bn128">
        %1 = array.read %arg0[%0] : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        %felt_const_0 = felt.const  0 : <"bn128">
        %2 = cast.toindex %felt_const_0 : !felt.type<"bn128">
        %3 = array.read %arg0[%2] : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        %4 = felt.sub %1, %3 : !felt.type<"bn128">, !felt.type<"bn128">
        pod.write %pod_0[@in] = %4 : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        %5 = pod.read %pod[@count] : <[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>, index
        %c1_1 = arith.constant 1 : index
        %6 = arith.subi %5, %c1_1 : index
        pod.write %pod[@count] = %6 : <[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>, index
        %c0 = arith.constant 0 : index
        %7 = arith.cmpi eq, %6, %c0 : index
        scf.if %7 {
          %11 = pod.read %pod_0[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
          %12 = function.call @IsZero_0::@IsZero_0::@compute(%11) : (!felt.type<"bn128">) -> !struct.type<@IsZero_0::@IsZero_0<[]>> 
          pod.write %pod[@comp] = %12 : <[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsZero_0::@IsZero_0<[]>>
        } else {
        }
        %8 = pod.read %pod[@comp] : <[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsZero_0::@IsZero_0<[]>>
        %9 = struct.readm %8[@out] : <@IsZero_0::@IsZero_0<[]>>, !felt.type<"bn128">
        struct.writem %self[@out] = %9 : <@IsEqual_1::@IsEqual_1<[]>>, !felt.type<"bn128">
        struct.writem %self[@isz$inputs] = %pod_0 : <@IsEqual_1::@IsEqual_1<[]>>, !pod.type<[@in: !felt.type<"bn128">]>
        %10 = pod.read %pod[@comp] : <[@count: index, @comp: !struct.type<@IsZero_0::@IsZero_0<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsZero_0::@IsZero_0<[]>>
        struct.writem %self[@isz] = %10 : <@IsEqual_1::@IsEqual_1<[]>>, !struct.type<@IsZero_0::@IsZero_0<[]>>
        function.return %self : !struct.type<@IsEqual_1::@IsEqual_1<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, %arg1: !array.type<2 x !felt.type<"bn128">>) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@out] : <@IsEqual_1::@IsEqual_1<[]>>, !felt.type<"bn128">
        %1 = struct.readm %arg0[@isz] : <@IsEqual_1::@IsEqual_1<[]>>, !struct.type<@IsZero_0::@IsZero_0<[]>>
        %2 = struct.readm %arg0[@isz$inputs] : <@IsEqual_1::@IsEqual_1<[]>>, !pod.type<[@in: !felt.type<"bn128">]>
        %felt_const_1 = felt.const  1 : <"bn128">
        %3 = cast.toindex %felt_const_1 : !felt.type<"bn128">
        %4 = array.read %arg1[%3] : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        %felt_const_0 = felt.const  0 : <"bn128">
        %5 = cast.toindex %felt_const_0 : !felt.type<"bn128">
        %6 = array.read %arg1[%5] : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        %7 = felt.sub %4, %6 : !felt.type<"bn128">, !felt.type<"bn128">
        %8 = pod.read %2[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        constrain.eq %8, %7 : !felt.type<"bn128">, !felt.type<"bn128">
        %9 = struct.readm %1[@out] : <@IsZero_0::@IsZero_0<[]>>, !felt.type<"bn128">
        constrain.eq %0, %9 : !felt.type<"bn128">, !felt.type<"bn128">
        %10 = pod.read %2[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        function.call @IsZero_0::@IsZero_0::@constrain(%1, %10) : (!struct.type<@IsZero_0::@IsZero_0<[]>>, !felt.type<"bn128">) -> () 
        function.return
      }
    }
  }
}
