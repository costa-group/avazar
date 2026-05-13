module attributes {llzk.lang, llzk.main = !struct.type<@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>} {
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
  poly.template @igualdadRepetida_2 {
    struct.def @igualdadRepetida_2 {
      struct.member @out : !felt.type<"bn128"> {llzk.pub}
      struct.member @cmp : !struct.type<@IsEqual_1::@IsEqual_1<[]>>
      struct.member @cmp$inputs : !pod.type<[@in: !array.type<2 x !felt.type<"bn128">>]>
      function.def @compute(%arg0: !felt.type<"bn128">) -> !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@igualdadRepetida_2::@igualdadRepetida_2<[]>>
        %c2 = arith.constant 2 : index
        %pod = pod.new { @count = %c2 }  : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>
        %pod_0 = pod.new : <[@in: !array.type<2 x !felt.type<"bn128">>]>
        %felt_const_0 = felt.const  0 : <"bn128">
        %0 = pod.read %pod_0[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        %felt_const_0_1 = felt.const  0 : <"bn128">
        %1 = cast.toindex %felt_const_0_1 : !felt.type<"bn128">
        array.write %0[%1] = %arg0 : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        pod.write %pod_0[@in] = %0 : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        %2 = pod.read %pod[@count] : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, index
        %c1 = arith.constant 1 : index
        %3 = arith.subi %2, %c1 : index
        pod.write %pod[@count] = %3 : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, index
        %c0 = arith.constant 0 : index
        %4 = arith.cmpi eq, %3, %c0 : index
        scf.if %4 {
          %13 = pod.read %pod_0[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
          %14 = function.call @IsEqual_1::@IsEqual_1::@compute(%13) : (!array.type<2 x !felt.type<"bn128">>) -> !struct.type<@IsEqual_1::@IsEqual_1<[]>> 
          pod.write %pod[@comp] = %14 : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsEqual_1::@IsEqual_1<[]>>
        } else {
        }
        %felt_const_0_2 = felt.const  0 : <"bn128">
        %5 = pod.read %pod_0[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        %felt_const_1 = felt.const  1 : <"bn128">
        %6 = cast.toindex %felt_const_1 : !felt.type<"bn128">
        array.write %5[%6] = %felt_const_0_2 : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        pod.write %pod_0[@in] = %5 : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        %7 = pod.read %pod[@count] : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, index
        %c1_3 = arith.constant 1 : index
        %8 = arith.subi %7, %c1_3 : index
        pod.write %pod[@count] = %8 : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, index
        %c0_4 = arith.constant 0 : index
        %9 = arith.cmpi eq, %8, %c0_4 : index
        scf.if %9 {
          %13 = pod.read %pod_0[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
          %14 = function.call @IsEqual_1::@IsEqual_1::@compute(%13) : (!array.type<2 x !felt.type<"bn128">>) -> !struct.type<@IsEqual_1::@IsEqual_1<[]>> 
          pod.write %pod[@comp] = %14 : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsEqual_1::@IsEqual_1<[]>>
        } else {
        }
        %10 = pod.read %pod[@comp] : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsEqual_1::@IsEqual_1<[]>>
        %11 = struct.readm %10[@out] : <@IsEqual_1::@IsEqual_1<[]>>, !felt.type<"bn128">
        struct.writem %self[@out] = %11 : <@igualdadRepetida_2::@igualdadRepetida_2<[]>>, !felt.type<"bn128">
        struct.writem %self[@cmp$inputs] = %pod_0 : <@igualdadRepetida_2::@igualdadRepetida_2<[]>>, !pod.type<[@in: !array.type<2 x !felt.type<"bn128">>]>
        %12 = pod.read %pod[@comp] : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsEqual_1::@IsEqual_1<[]>>
        struct.writem %self[@cmp] = %12 : <@igualdadRepetida_2::@igualdadRepetida_2<[]>>, !struct.type<@IsEqual_1::@IsEqual_1<[]>>
        function.return %self : !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>, %arg1: !felt.type<"bn128">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@out] : <@igualdadRepetida_2::@igualdadRepetida_2<[]>>, !felt.type<"bn128">
        %1 = struct.readm %arg0[@cmp] : <@igualdadRepetida_2::@igualdadRepetida_2<[]>>, !struct.type<@IsEqual_1::@IsEqual_1<[]>>
        %2 = struct.readm %arg0[@cmp$inputs] : <@igualdadRepetida_2::@igualdadRepetida_2<[]>>, !pod.type<[@in: !array.type<2 x !felt.type<"bn128">>]>
        %felt_const_0 = felt.const  0 : <"bn128">
        %3 = pod.read %2[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        %felt_const_0_0 = felt.const  0 : <"bn128">
        %4 = cast.toindex %felt_const_0_0 : !felt.type<"bn128">
        %5 = array.read %3[%4] : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        constrain.eq %5, %arg1 : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_0_1 = felt.const  0 : <"bn128">
        %6 = pod.read %2[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        %felt_const_1 = felt.const  1 : <"bn128">
        %7 = cast.toindex %felt_const_1 : !felt.type<"bn128">
        %8 = array.read %6[%7] : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        constrain.eq %8, %felt_const_0_1 : !felt.type<"bn128">, !felt.type<"bn128">
        %9 = struct.readm %1[@out] : <@IsEqual_1::@IsEqual_1<[]>>, !felt.type<"bn128">
        constrain.eq %0, %9 : !felt.type<"bn128">, !felt.type<"bn128">
        %10 = pod.read %2[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        function.call @IsEqual_1::@IsEqual_1::@constrain(%1, %10) : (!struct.type<@IsEqual_1::@IsEqual_1<[]>>, !array.type<2 x !felt.type<"bn128">>) -> () 
        function.return
      }
    }
  }
  poly.template @igualdadRepetida_3 {
    struct.def @igualdadRepetida_3 {
      struct.member @out : !felt.type<"bn128"> {llzk.pub}
      struct.member @cmp : !struct.type<@IsEqual_1::@IsEqual_1<[]>>
      struct.member @cmp$inputs : !pod.type<[@in: !array.type<2 x !felt.type<"bn128">>]>
      function.def @compute(%arg0: !felt.type<"bn128">) -> !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@igualdadRepetida_3::@igualdadRepetida_3<[]>>
        %c2 = arith.constant 2 : index
        %pod = pod.new { @count = %c2 }  : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>
        %pod_0 = pod.new : <[@in: !array.type<2 x !felt.type<"bn128">>]>
        %felt_const_1 = felt.const  1 : <"bn128">
        %0 = pod.read %pod_0[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        %felt_const_0 = felt.const  0 : <"bn128">
        %1 = cast.toindex %felt_const_0 : !felt.type<"bn128">
        array.write %0[%1] = %arg0 : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        pod.write %pod_0[@in] = %0 : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        %2 = pod.read %pod[@count] : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, index
        %c1 = arith.constant 1 : index
        %3 = arith.subi %2, %c1 : index
        pod.write %pod[@count] = %3 : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, index
        %c0 = arith.constant 0 : index
        %4 = arith.cmpi eq, %3, %c0 : index
        scf.if %4 {
          %13 = pod.read %pod_0[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
          %14 = function.call @IsEqual_1::@IsEqual_1::@compute(%13) : (!array.type<2 x !felt.type<"bn128">>) -> !struct.type<@IsEqual_1::@IsEqual_1<[]>> 
          pod.write %pod[@comp] = %14 : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsEqual_1::@IsEqual_1<[]>>
        } else {
        }
        %felt_const_1_1 = felt.const  1 : <"bn128">
        %5 = pod.read %pod_0[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        %felt_const_1_2 = felt.const  1 : <"bn128">
        %6 = cast.toindex %felt_const_1_2 : !felt.type<"bn128">
        array.write %5[%6] = %felt_const_1_1 : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        pod.write %pod_0[@in] = %5 : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        %7 = pod.read %pod[@count] : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, index
        %c1_3 = arith.constant 1 : index
        %8 = arith.subi %7, %c1_3 : index
        pod.write %pod[@count] = %8 : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, index
        %c0_4 = arith.constant 0 : index
        %9 = arith.cmpi eq, %8, %c0_4 : index
        scf.if %9 {
          %13 = pod.read %pod_0[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
          %14 = function.call @IsEqual_1::@IsEqual_1::@compute(%13) : (!array.type<2 x !felt.type<"bn128">>) -> !struct.type<@IsEqual_1::@IsEqual_1<[]>> 
          pod.write %pod[@comp] = %14 : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsEqual_1::@IsEqual_1<[]>>
        } else {
        }
        %10 = pod.read %pod[@comp] : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsEqual_1::@IsEqual_1<[]>>
        %11 = struct.readm %10[@out] : <@IsEqual_1::@IsEqual_1<[]>>, !felt.type<"bn128">
        struct.writem %self[@out] = %11 : <@igualdadRepetida_3::@igualdadRepetida_3<[]>>, !felt.type<"bn128">
        struct.writem %self[@cmp$inputs] = %pod_0 : <@igualdadRepetida_3::@igualdadRepetida_3<[]>>, !pod.type<[@in: !array.type<2 x !felt.type<"bn128">>]>
        %12 = pod.read %pod[@comp] : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsEqual_1::@IsEqual_1<[]>>
        struct.writem %self[@cmp] = %12 : <@igualdadRepetida_3::@igualdadRepetida_3<[]>>, !struct.type<@IsEqual_1::@IsEqual_1<[]>>
        function.return %self : !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>, %arg1: !felt.type<"bn128">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@out] : <@igualdadRepetida_3::@igualdadRepetida_3<[]>>, !felt.type<"bn128">
        %1 = struct.readm %arg0[@cmp] : <@igualdadRepetida_3::@igualdadRepetida_3<[]>>, !struct.type<@IsEqual_1::@IsEqual_1<[]>>
        %2 = struct.readm %arg0[@cmp$inputs] : <@igualdadRepetida_3::@igualdadRepetida_3<[]>>, !pod.type<[@in: !array.type<2 x !felt.type<"bn128">>]>
        %felt_const_1 = felt.const  1 : <"bn128">
        %3 = pod.read %2[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        %felt_const_0 = felt.const  0 : <"bn128">
        %4 = cast.toindex %felt_const_0 : !felt.type<"bn128">
        %5 = array.read %3[%4] : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        constrain.eq %5, %arg1 : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_1_0 = felt.const  1 : <"bn128">
        %6 = pod.read %2[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        %felt_const_1_1 = felt.const  1 : <"bn128">
        %7 = cast.toindex %felt_const_1_1 : !felt.type<"bn128">
        %8 = array.read %6[%7] : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        constrain.eq %8, %felt_const_1_0 : !felt.type<"bn128">, !felt.type<"bn128">
        %9 = struct.readm %1[@out] : <@IsEqual_1::@IsEqual_1<[]>>, !felt.type<"bn128">
        constrain.eq %0, %9 : !felt.type<"bn128">, !felt.type<"bn128">
        %10 = pod.read %2[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        function.call @IsEqual_1::@IsEqual_1::@constrain(%1, %10) : (!struct.type<@IsEqual_1::@IsEqual_1<[]>>, !array.type<2 x !felt.type<"bn128">>) -> () 
        function.return
      }
    }
  }
  poly.template @igualdadRepetida_4 {
    struct.def @igualdadRepetida_4 {
      struct.member @out : !felt.type<"bn128"> {llzk.pub}
      struct.member @cmp : !struct.type<@IsEqual_1::@IsEqual_1<[]>>
      struct.member @cmp$inputs : !pod.type<[@in: !array.type<2 x !felt.type<"bn128">>]>
      function.def @compute(%arg0: !felt.type<"bn128">) -> !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@igualdadRepetida_4::@igualdadRepetida_4<[]>>
        %c2 = arith.constant 2 : index
        %pod = pod.new { @count = %c2 }  : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>
        %pod_0 = pod.new : <[@in: !array.type<2 x !felt.type<"bn128">>]>
        %felt_const_2 = felt.const  2 : <"bn128">
        %0 = pod.read %pod_0[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        %felt_const_0 = felt.const  0 : <"bn128">
        %1 = cast.toindex %felt_const_0 : !felt.type<"bn128">
        array.write %0[%1] = %arg0 : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        pod.write %pod_0[@in] = %0 : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        %2 = pod.read %pod[@count] : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, index
        %c1 = arith.constant 1 : index
        %3 = arith.subi %2, %c1 : index
        pod.write %pod[@count] = %3 : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, index
        %c0 = arith.constant 0 : index
        %4 = arith.cmpi eq, %3, %c0 : index
        scf.if %4 {
          %13 = pod.read %pod_0[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
          %14 = function.call @IsEqual_1::@IsEqual_1::@compute(%13) : (!array.type<2 x !felt.type<"bn128">>) -> !struct.type<@IsEqual_1::@IsEqual_1<[]>> 
          pod.write %pod[@comp] = %14 : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsEqual_1::@IsEqual_1<[]>>
        } else {
        }
        %felt_const_2_1 = felt.const  2 : <"bn128">
        %5 = pod.read %pod_0[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        %felt_const_1 = felt.const  1 : <"bn128">
        %6 = cast.toindex %felt_const_1 : !felt.type<"bn128">
        array.write %5[%6] = %felt_const_2_1 : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        pod.write %pod_0[@in] = %5 : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        %7 = pod.read %pod[@count] : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, index
        %c1_2 = arith.constant 1 : index
        %8 = arith.subi %7, %c1_2 : index
        pod.write %pod[@count] = %8 : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, index
        %c0_3 = arith.constant 0 : index
        %9 = arith.cmpi eq, %8, %c0_3 : index
        scf.if %9 {
          %13 = pod.read %pod_0[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
          %14 = function.call @IsEqual_1::@IsEqual_1::@compute(%13) : (!array.type<2 x !felt.type<"bn128">>) -> !struct.type<@IsEqual_1::@IsEqual_1<[]>> 
          pod.write %pod[@comp] = %14 : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsEqual_1::@IsEqual_1<[]>>
        } else {
        }
        %10 = pod.read %pod[@comp] : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsEqual_1::@IsEqual_1<[]>>
        %11 = struct.readm %10[@out] : <@IsEqual_1::@IsEqual_1<[]>>, !felt.type<"bn128">
        struct.writem %self[@out] = %11 : <@igualdadRepetida_4::@igualdadRepetida_4<[]>>, !felt.type<"bn128">
        struct.writem %self[@cmp$inputs] = %pod_0 : <@igualdadRepetida_4::@igualdadRepetida_4<[]>>, !pod.type<[@in: !array.type<2 x !felt.type<"bn128">>]>
        %12 = pod.read %pod[@comp] : <[@count: index, @comp: !struct.type<@IsEqual_1::@IsEqual_1<[]>>, @params: !pod.type<[]>]>, !struct.type<@IsEqual_1::@IsEqual_1<[]>>
        struct.writem %self[@cmp] = %12 : <@igualdadRepetida_4::@igualdadRepetida_4<[]>>, !struct.type<@IsEqual_1::@IsEqual_1<[]>>
        function.return %self : !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>, %arg1: !felt.type<"bn128">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@out] : <@igualdadRepetida_4::@igualdadRepetida_4<[]>>, !felt.type<"bn128">
        %1 = struct.readm %arg0[@cmp] : <@igualdadRepetida_4::@igualdadRepetida_4<[]>>, !struct.type<@IsEqual_1::@IsEqual_1<[]>>
        %2 = struct.readm %arg0[@cmp$inputs] : <@igualdadRepetida_4::@igualdadRepetida_4<[]>>, !pod.type<[@in: !array.type<2 x !felt.type<"bn128">>]>
        %felt_const_2 = felt.const  2 : <"bn128">
        %3 = pod.read %2[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        %felt_const_0 = felt.const  0 : <"bn128">
        %4 = cast.toindex %felt_const_0 : !felt.type<"bn128">
        %5 = array.read %3[%4] : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        constrain.eq %5, %arg1 : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_2_0 = felt.const  2 : <"bn128">
        %6 = pod.read %2[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        %felt_const_1 = felt.const  1 : <"bn128">
        %7 = cast.toindex %felt_const_1 : !felt.type<"bn128">
        %8 = array.read %6[%7] : <2 x !felt.type<"bn128">>, !felt.type<"bn128">
        constrain.eq %8, %felt_const_2_0 : !felt.type<"bn128">, !felt.type<"bn128">
        %9 = struct.readm %1[@out] : <@IsEqual_1::@IsEqual_1<[]>>, !felt.type<"bn128">
        constrain.eq %0, %9 : !felt.type<"bn128">, !felt.type<"bn128">
        %10 = pod.read %2[@in] : <[@in: !array.type<2 x !felt.type<"bn128">>]>, !array.type<2 x !felt.type<"bn128">>
        function.call @IsEqual_1::@IsEqual_1::@constrain(%1, %10) : (!struct.type<@IsEqual_1::@IsEqual_1<[]>>, !array.type<2 x !felt.type<"bn128">>) -> () 
        function.return
      }
    }
  }
  poly.template @piedra_papel_tijera_5 {
    struct.def @piedra_papel_tijera_5 {
      struct.member @ganador : !felt.type<"bn128"> {llzk.pub}
      struct.member @eq : !felt.type<"bn128">
      struct.member @inv : !felt.type<"bn128">
      struct.member @out : !felt.type<"bn128">
      struct.member @j1 : !felt.type<"bn128">
      struct.member @j2 : !felt.type<"bn128">
      struct.member @eq0 : !felt.type<"bn128">
      struct.member @eq1 : !felt.type<"bn128">
      struct.member @eq2 : !felt.type<"bn128">
      struct.member @j1_0 : !felt.type<"bn128">
      struct.member @j1_1 : !felt.type<"bn128">
      struct.member @j1_2 : !felt.type<"bn128">
      struct.member @j2_0 : !felt.type<"bn128">
      struct.member @j2_1 : !felt.type<"bn128">
      struct.member @j2_2 : !felt.type<"bn128">
      struct.member @J1_1 : !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>
      struct.member @J1_1$inputs : !pod.type<[@in: !felt.type<"bn128">]>
      struct.member @J2_2 : !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>
      struct.member @J2_2$inputs : !pod.type<[@in: !felt.type<"bn128">]>
      struct.member @J1_0 : !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>
      struct.member @J1_0$inputs : !pod.type<[@in: !felt.type<"bn128">]>
      struct.member @J1_2 : !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>
      struct.member @J1_2$inputs : !pod.type<[@in: !felt.type<"bn128">]>
      struct.member @J2_0 : !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>
      struct.member @J2_0$inputs : !pod.type<[@in: !felt.type<"bn128">]>
      struct.member @J2_1 : !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>
      struct.member @J2_1$inputs : !pod.type<[@in: !felt.type<"bn128">]>
      function.def @compute(%arg0: !felt.type<"bn128">, %arg1: !felt.type<"bn128">) -> !struct.type<@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>> attributes {function.allow_non_native_field_ops, function.allow_witness} {
        %self = struct.new : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>
        %c1 = arith.constant 1 : index
        %pod = pod.new { @count = %c1 }  : <[@count: index, @comp: !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>, @params: !pod.type<[]>]>
        %pod_0 = pod.new : <[@in: !felt.type<"bn128">]>
        %c1_1 = arith.constant 1 : index
        %pod_2 = pod.new { @count = %c1_1 }  : <[@count: index, @comp: !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>, @params: !pod.type<[]>]>
        %pod_3 = pod.new : <[@in: !felt.type<"bn128">]>
        %c1_4 = arith.constant 1 : index
        %pod_5 = pod.new { @count = %c1_4 }  : <[@count: index, @comp: !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>, @params: !pod.type<[]>]>
        %pod_6 = pod.new : <[@in: !felt.type<"bn128">]>
        %c1_7 = arith.constant 1 : index
        %pod_8 = pod.new { @count = %c1_7 }  : <[@count: index, @comp: !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>, @params: !pod.type<[]>]>
        %pod_9 = pod.new : <[@in: !felt.type<"bn128">]>
        %c1_10 = arith.constant 1 : index
        %pod_11 = pod.new { @count = %c1_10 }  : <[@count: index, @comp: !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>, @params: !pod.type<[]>]>
        %pod_12 = pod.new : <[@in: !felt.type<"bn128">]>
        %c1_13 = arith.constant 1 : index
        %pod_14 = pod.new { @count = %c1_13 }  : <[@count: index, @comp: !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>, @params: !pod.type<[]>]>
        %pod_15 = pod.new : <[@in: !felt.type<"bn128">]>
        pod.write %pod_6[@in] = %arg0 : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        %0 = pod.read %pod_5[@count] : <[@count: index, @comp: !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>, @params: !pod.type<[]>]>, index
        %c1_16 = arith.constant 1 : index
        %1 = arith.subi %0, %c1_16 : index
        pod.write %pod_5[@count] = %1 : <[@count: index, @comp: !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>, @params: !pod.type<[]>]>, index
        %c0 = arith.constant 0 : index
        %2 = arith.cmpi eq, %1, %c0 : index
        scf.if %2 {
          %83 = pod.read %pod_6[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
          %84 = function.call @igualdadRepetida_2::@igualdadRepetida_2::@compute(%83) : (!felt.type<"bn128">) -> !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>> 
          pod.write %pod_5[@comp] = %84 : <[@count: index, @comp: !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>
        } else {
        }
        pod.write %pod_0[@in] = %arg0 : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        %3 = pod.read %pod[@count] : <[@count: index, @comp: !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>, @params: !pod.type<[]>]>, index
        %c1_17 = arith.constant 1 : index
        %4 = arith.subi %3, %c1_17 : index
        pod.write %pod[@count] = %4 : <[@count: index, @comp: !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>, @params: !pod.type<[]>]>, index
        %c0_18 = arith.constant 0 : index
        %5 = arith.cmpi eq, %4, %c0_18 : index
        scf.if %5 {
          %83 = pod.read %pod_0[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
          %84 = function.call @igualdadRepetida_3::@igualdadRepetida_3::@compute(%83) : (!felt.type<"bn128">) -> !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>> 
          pod.write %pod[@comp] = %84 : <[@count: index, @comp: !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>
        } else {
        }
        pod.write %pod_9[@in] = %arg0 : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        %6 = pod.read %pod_8[@count] : <[@count: index, @comp: !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>, @params: !pod.type<[]>]>, index
        %c1_19 = arith.constant 1 : index
        %7 = arith.subi %6, %c1_19 : index
        pod.write %pod_8[@count] = %7 : <[@count: index, @comp: !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>, @params: !pod.type<[]>]>, index
        %c0_20 = arith.constant 0 : index
        %8 = arith.cmpi eq, %7, %c0_20 : index
        scf.if %8 {
          %83 = pod.read %pod_9[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
          %84 = function.call @igualdadRepetida_4::@igualdadRepetida_4::@compute(%83) : (!felt.type<"bn128">) -> !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>> 
          pod.write %pod_8[@comp] = %84 : <[@count: index, @comp: !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>
        } else {
        }
        pod.write %pod_12[@in] = %arg1 : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        %9 = pod.read %pod_11[@count] : <[@count: index, @comp: !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>, @params: !pod.type<[]>]>, index
        %c1_21 = arith.constant 1 : index
        %10 = arith.subi %9, %c1_21 : index
        pod.write %pod_11[@count] = %10 : <[@count: index, @comp: !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>, @params: !pod.type<[]>]>, index
        %c0_22 = arith.constant 0 : index
        %11 = arith.cmpi eq, %10, %c0_22 : index
        scf.if %11 {
          %83 = pod.read %pod_12[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
          %84 = function.call @igualdadRepetida_2::@igualdadRepetida_2::@compute(%83) : (!felt.type<"bn128">) -> !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>> 
          pod.write %pod_11[@comp] = %84 : <[@count: index, @comp: !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>
        } else {
        }
        pod.write %pod_15[@in] = %arg1 : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        %12 = pod.read %pod_14[@count] : <[@count: index, @comp: !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>, @params: !pod.type<[]>]>, index
        %c1_23 = arith.constant 1 : index
        %13 = arith.subi %12, %c1_23 : index
        pod.write %pod_14[@count] = %13 : <[@count: index, @comp: !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>, @params: !pod.type<[]>]>, index
        %c0_24 = arith.constant 0 : index
        %14 = arith.cmpi eq, %13, %c0_24 : index
        scf.if %14 {
          %83 = pod.read %pod_15[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
          %84 = function.call @igualdadRepetida_3::@igualdadRepetida_3::@compute(%83) : (!felt.type<"bn128">) -> !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>> 
          pod.write %pod_14[@comp] = %84 : <[@count: index, @comp: !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>
        } else {
        }
        pod.write %pod_3[@in] = %arg1 : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        %15 = pod.read %pod_2[@count] : <[@count: index, @comp: !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>, @params: !pod.type<[]>]>, index
        %c1_25 = arith.constant 1 : index
        %16 = arith.subi %15, %c1_25 : index
        pod.write %pod_2[@count] = %16 : <[@count: index, @comp: !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>, @params: !pod.type<[]>]>, index
        %c0_26 = arith.constant 0 : index
        %17 = arith.cmpi eq, %16, %c0_26 : index
        scf.if %17 {
          %83 = pod.read %pod_3[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
          %84 = function.call @igualdadRepetida_4::@igualdadRepetida_4::@compute(%83) : (!felt.type<"bn128">) -> !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>> 
          pod.write %pod_2[@comp] = %84 : <[@count: index, @comp: !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>
        } else {
        }
        %18 = pod.read %pod_5[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>
        %19 = struct.readm %18[@out] : <@igualdadRepetida_2::@igualdadRepetida_2<[]>>, !felt.type<"bn128">
        %20 = pod.read %pod_11[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>
        %21 = struct.readm %20[@out] : <@igualdadRepetida_2::@igualdadRepetida_2<[]>>, !felt.type<"bn128">
        %22 = felt.mul %19, %21 : !felt.type<"bn128">, !felt.type<"bn128">
        struct.writem %self[@eq0] = %22 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %23 = pod.read %pod[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>
        %24 = struct.readm %23[@out] : <@igualdadRepetida_3::@igualdadRepetida_3<[]>>, !felt.type<"bn128">
        %25 = pod.read %pod_14[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>
        %26 = struct.readm %25[@out] : <@igualdadRepetida_3::@igualdadRepetida_3<[]>>, !felt.type<"bn128">
        %27 = felt.mul %24, %26 : !felt.type<"bn128">, !felt.type<"bn128">
        struct.writem %self[@eq1] = %27 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %28 = pod.read %pod_8[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>
        %29 = struct.readm %28[@out] : <@igualdadRepetida_4::@igualdadRepetida_4<[]>>, !felt.type<"bn128">
        %30 = pod.read %pod_2[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>
        %31 = struct.readm %30[@out] : <@igualdadRepetida_4::@igualdadRepetida_4<[]>>, !felt.type<"bn128">
        %32 = felt.mul %29, %31 : !felt.type<"bn128">, !felt.type<"bn128">
        struct.writem %self[@eq2] = %32 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %33 = felt.add %22, %27 : !felt.type<"bn128">, !felt.type<"bn128">
        %34 = felt.add %33, %32 : !felt.type<"bn128">, !felt.type<"bn128">
        struct.writem %self[@eq] = %34 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %felt_const_1 = felt.const  1 : <"bn128">
        %35 = felt.sub %felt_const_1, %34 : !felt.type<"bn128">, !felt.type<"bn128">
        struct.writem %self[@inv] = %35 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %36 = pod.read %pod_5[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>
        %37 = struct.readm %36[@out] : <@igualdadRepetida_2::@igualdadRepetida_2<[]>>, !felt.type<"bn128">
        %38 = pod.read %pod_2[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>
        %39 = struct.readm %38[@out] : <@igualdadRepetida_4::@igualdadRepetida_4<[]>>, !felt.type<"bn128">
        %40 = felt.mul %37, %39 : !felt.type<"bn128">, !felt.type<"bn128">
        struct.writem %self[@j1_0] = %40 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %41 = pod.read %pod[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>
        %42 = struct.readm %41[@out] : <@igualdadRepetida_3::@igualdadRepetida_3<[]>>, !felt.type<"bn128">
        %43 = pod.read %pod_11[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>
        %44 = struct.readm %43[@out] : <@igualdadRepetida_2::@igualdadRepetida_2<[]>>, !felt.type<"bn128">
        %45 = felt.mul %42, %44 : !felt.type<"bn128">, !felt.type<"bn128">
        struct.writem %self[@j1_1] = %45 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %46 = pod.read %pod_8[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>
        %47 = struct.readm %46[@out] : <@igualdadRepetida_4::@igualdadRepetida_4<[]>>, !felt.type<"bn128">
        %48 = pod.read %pod_14[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>
        %49 = struct.readm %48[@out] : <@igualdadRepetida_3::@igualdadRepetida_3<[]>>, !felt.type<"bn128">
        %50 = felt.mul %47, %49 : !felt.type<"bn128">, !felt.type<"bn128">
        struct.writem %self[@j1_2] = %50 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %51 = felt.add %40, %45 : !felt.type<"bn128">, !felt.type<"bn128">
        %52 = felt.add %51, %50 : !felt.type<"bn128">, !felt.type<"bn128">
        struct.writem %self[@j1] = %52 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %53 = pod.read %pod_5[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>
        %54 = struct.readm %53[@out] : <@igualdadRepetida_2::@igualdadRepetida_2<[]>>, !felt.type<"bn128">
        %55 = pod.read %pod_14[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>
        %56 = struct.readm %55[@out] : <@igualdadRepetida_3::@igualdadRepetida_3<[]>>, !felt.type<"bn128">
        %57 = felt.mul %54, %56 : !felt.type<"bn128">, !felt.type<"bn128">
        struct.writem %self[@j2_0] = %57 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %58 = pod.read %pod[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>
        %59 = struct.readm %58[@out] : <@igualdadRepetida_3::@igualdadRepetida_3<[]>>, !felt.type<"bn128">
        %60 = pod.read %pod_2[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>
        %61 = struct.readm %60[@out] : <@igualdadRepetida_4::@igualdadRepetida_4<[]>>, !felt.type<"bn128">
        %62 = felt.mul %59, %61 : !felt.type<"bn128">, !felt.type<"bn128">
        struct.writem %self[@j2_1] = %62 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %63 = pod.read %pod_8[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>
        %64 = struct.readm %63[@out] : <@igualdadRepetida_4::@igualdadRepetida_4<[]>>, !felt.type<"bn128">
        %65 = pod.read %pod_11[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>
        %66 = struct.readm %65[@out] : <@igualdadRepetida_2::@igualdadRepetida_2<[]>>, !felt.type<"bn128">
        %67 = felt.mul %64, %66 : !felt.type<"bn128">, !felt.type<"bn128">
        struct.writem %self[@j2_2] = %67 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %68 = felt.add %57, %62 : !felt.type<"bn128">, !felt.type<"bn128">
        %69 = felt.add %68, %67 : !felt.type<"bn128">, !felt.type<"bn128">
        struct.writem %self[@j2] = %69 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %felt_const_1_27 = felt.const  1 : <"bn128">
        %70 = felt.mul %69, %felt_const_1_27 : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_0 = felt.const  0 : <"bn128">
        %71 = felt.mul %52, %felt_const_0 : !felt.type<"bn128">, !felt.type<"bn128">
        %72 = felt.add %70, %71 : !felt.type<"bn128">, !felt.type<"bn128">
        struct.writem %self[@out] = %72 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %felt_const_1_28 = felt.const  1 : <"bn128">
        %73 = felt.sub %felt_const_1_28, %35 : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_2 = felt.const  2 : <"bn128">
        %74 = felt.mul %73, %felt_const_2 : !felt.type<"bn128">, !felt.type<"bn128">
        %75 = felt.mul %72, %35 : !felt.type<"bn128">, !felt.type<"bn128">
        %76 = felt.add %74, %75 : !felt.type<"bn128">, !felt.type<"bn128">
        struct.writem %self[@ganador] = %76 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        struct.writem %self[@J1_2$inputs] = %pod_9 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !pod.type<[@in: !felt.type<"bn128">]>
        %77 = pod.read %pod_8[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>
        struct.writem %self[@J1_2] = %77 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>
        struct.writem %self[@J1_0$inputs] = %pod_6 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !pod.type<[@in: !felt.type<"bn128">]>
        %78 = pod.read %pod_5[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>
        struct.writem %self[@J1_0] = %78 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>
        struct.writem %self[@J2_1$inputs] = %pod_15 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !pod.type<[@in: !felt.type<"bn128">]>
        %79 = pod.read %pod_14[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>
        struct.writem %self[@J2_1] = %79 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>
        struct.writem %self[@J1_1$inputs] = %pod_0 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !pod.type<[@in: !felt.type<"bn128">]>
        %80 = pod.read %pod[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>
        struct.writem %self[@J1_1] = %80 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>
        struct.writem %self[@J2_2$inputs] = %pod_3 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !pod.type<[@in: !felt.type<"bn128">]>
        %81 = pod.read %pod_2[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>
        struct.writem %self[@J2_2] = %81 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>
        struct.writem %self[@J2_0$inputs] = %pod_12 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !pod.type<[@in: !felt.type<"bn128">]>
        %82 = pod.read %pod_11[@comp] : <[@count: index, @comp: !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>, @params: !pod.type<[]>]>, !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>
        struct.writem %self[@J2_0] = %82 : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>
        function.return %self : !struct.type<@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>
      }
      function.def @constrain(%arg0: !struct.type<@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, %arg1: !felt.type<"bn128">, %arg2: !felt.type<"bn128">) attributes {function.allow_constraint, function.allow_non_native_field_ops} {
        %0 = struct.readm %arg0[@ganador] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %1 = struct.readm %arg0[@eq] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %2 = struct.readm %arg0[@inv] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %3 = struct.readm %arg0[@out] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %4 = struct.readm %arg0[@j1] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %5 = struct.readm %arg0[@j2] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %6 = struct.readm %arg0[@eq0] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %7 = struct.readm %arg0[@eq1] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %8 = struct.readm %arg0[@eq2] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %9 = struct.readm %arg0[@j1_0] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %10 = struct.readm %arg0[@j1_1] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %11 = struct.readm %arg0[@j1_2] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %12 = struct.readm %arg0[@j2_0] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %13 = struct.readm %arg0[@j2_1] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %14 = struct.readm %arg0[@j2_2] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !felt.type<"bn128">
        %15 = struct.readm %arg0[@J1_1] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>
        %16 = struct.readm %arg0[@J1_1$inputs] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !pod.type<[@in: !felt.type<"bn128">]>
        %17 = struct.readm %arg0[@J2_2] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>
        %18 = struct.readm %arg0[@J2_2$inputs] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !pod.type<[@in: !felt.type<"bn128">]>
        %19 = struct.readm %arg0[@J1_0] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>
        %20 = struct.readm %arg0[@J1_0$inputs] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !pod.type<[@in: !felt.type<"bn128">]>
        %21 = struct.readm %arg0[@J1_2] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>
        %22 = struct.readm %arg0[@J1_2$inputs] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !pod.type<[@in: !felt.type<"bn128">]>
        %23 = struct.readm %arg0[@J2_0] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>
        %24 = struct.readm %arg0[@J2_0$inputs] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !pod.type<[@in: !felt.type<"bn128">]>
        %25 = struct.readm %arg0[@J2_1] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>
        %26 = struct.readm %arg0[@J2_1$inputs] : <@piedra_papel_tijera_5::@piedra_papel_tijera_5<[]>>, !pod.type<[@in: !felt.type<"bn128">]>
        %27 = pod.read %20[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        constrain.eq %27, %arg1 : !felt.type<"bn128">, !felt.type<"bn128">
        %28 = pod.read %16[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        constrain.eq %28, %arg1 : !felt.type<"bn128">, !felt.type<"bn128">
        %29 = pod.read %22[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        constrain.eq %29, %arg1 : !felt.type<"bn128">, !felt.type<"bn128">
        %30 = pod.read %24[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        constrain.eq %30, %arg2 : !felt.type<"bn128">, !felt.type<"bn128">
        %31 = pod.read %26[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        constrain.eq %31, %arg2 : !felt.type<"bn128">, !felt.type<"bn128">
        %32 = pod.read %18[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        constrain.eq %32, %arg2 : !felt.type<"bn128">, !felt.type<"bn128">
        %33 = struct.readm %19[@out] : <@igualdadRepetida_2::@igualdadRepetida_2<[]>>, !felt.type<"bn128">
        %34 = struct.readm %23[@out] : <@igualdadRepetida_2::@igualdadRepetida_2<[]>>, !felt.type<"bn128">
        %35 = felt.mul %33, %34 : !felt.type<"bn128">, !felt.type<"bn128">
        constrain.eq %6, %35 : !felt.type<"bn128">, !felt.type<"bn128">
        %36 = struct.readm %15[@out] : <@igualdadRepetida_3::@igualdadRepetida_3<[]>>, !felt.type<"bn128">
        %37 = struct.readm %25[@out] : <@igualdadRepetida_3::@igualdadRepetida_3<[]>>, !felt.type<"bn128">
        %38 = felt.mul %36, %37 : !felt.type<"bn128">, !felt.type<"bn128">
        constrain.eq %7, %38 : !felt.type<"bn128">, !felt.type<"bn128">
        %39 = struct.readm %21[@out] : <@igualdadRepetida_4::@igualdadRepetida_4<[]>>, !felt.type<"bn128">
        %40 = struct.readm %17[@out] : <@igualdadRepetida_4::@igualdadRepetida_4<[]>>, !felt.type<"bn128">
        %41 = felt.mul %39, %40 : !felt.type<"bn128">, !felt.type<"bn128">
        constrain.eq %8, %41 : !felt.type<"bn128">, !felt.type<"bn128">
        %42 = felt.add %6, %7 : !felt.type<"bn128">, !felt.type<"bn128">
        %43 = felt.add %42, %8 : !felt.type<"bn128">, !felt.type<"bn128">
        constrain.eq %1, %43 : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_1 = felt.const  1 : <"bn128">
        %44 = felt.sub %felt_const_1, %1 : !felt.type<"bn128">, !felt.type<"bn128">
        constrain.eq %2, %44 : !felt.type<"bn128">, !felt.type<"bn128">
        %45 = struct.readm %19[@out] : <@igualdadRepetida_2::@igualdadRepetida_2<[]>>, !felt.type<"bn128">
        %46 = struct.readm %17[@out] : <@igualdadRepetida_4::@igualdadRepetida_4<[]>>, !felt.type<"bn128">
        %47 = felt.mul %45, %46 : !felt.type<"bn128">, !felt.type<"bn128">
        constrain.eq %9, %47 : !felt.type<"bn128">, !felt.type<"bn128">
        %48 = struct.readm %15[@out] : <@igualdadRepetida_3::@igualdadRepetida_3<[]>>, !felt.type<"bn128">
        %49 = struct.readm %23[@out] : <@igualdadRepetida_2::@igualdadRepetida_2<[]>>, !felt.type<"bn128">
        %50 = felt.mul %48, %49 : !felt.type<"bn128">, !felt.type<"bn128">
        constrain.eq %10, %50 : !felt.type<"bn128">, !felt.type<"bn128">
        %51 = struct.readm %21[@out] : <@igualdadRepetida_4::@igualdadRepetida_4<[]>>, !felt.type<"bn128">
        %52 = struct.readm %25[@out] : <@igualdadRepetida_3::@igualdadRepetida_3<[]>>, !felt.type<"bn128">
        %53 = felt.mul %51, %52 : !felt.type<"bn128">, !felt.type<"bn128">
        constrain.eq %11, %53 : !felt.type<"bn128">, !felt.type<"bn128">
        %54 = felt.add %9, %10 : !felt.type<"bn128">, !felt.type<"bn128">
        %55 = felt.add %54, %11 : !felt.type<"bn128">, !felt.type<"bn128">
        constrain.eq %4, %55 : !felt.type<"bn128">, !felt.type<"bn128">
        %56 = struct.readm %19[@out] : <@igualdadRepetida_2::@igualdadRepetida_2<[]>>, !felt.type<"bn128">
        %57 = struct.readm %25[@out] : <@igualdadRepetida_3::@igualdadRepetida_3<[]>>, !felt.type<"bn128">
        %58 = felt.mul %56, %57 : !felt.type<"bn128">, !felt.type<"bn128">
        constrain.eq %12, %58 : !felt.type<"bn128">, !felt.type<"bn128">
        %59 = struct.readm %15[@out] : <@igualdadRepetida_3::@igualdadRepetida_3<[]>>, !felt.type<"bn128">
        %60 = struct.readm %17[@out] : <@igualdadRepetida_4::@igualdadRepetida_4<[]>>, !felt.type<"bn128">
        %61 = felt.mul %59, %60 : !felt.type<"bn128">, !felt.type<"bn128">
        constrain.eq %13, %61 : !felt.type<"bn128">, !felt.type<"bn128">
        %62 = struct.readm %21[@out] : <@igualdadRepetida_4::@igualdadRepetida_4<[]>>, !felt.type<"bn128">
        %63 = struct.readm %23[@out] : <@igualdadRepetida_2::@igualdadRepetida_2<[]>>, !felt.type<"bn128">
        %64 = felt.mul %62, %63 : !felt.type<"bn128">, !felt.type<"bn128">
        constrain.eq %14, %64 : !felt.type<"bn128">, !felt.type<"bn128">
        %65 = felt.add %12, %13 : !felt.type<"bn128">, !felt.type<"bn128">
        %66 = felt.add %65, %14 : !felt.type<"bn128">, !felt.type<"bn128">
        constrain.eq %5, %66 : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_1_0 = felt.const  1 : <"bn128">
        %67 = felt.mul %5, %felt_const_1_0 : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_0 = felt.const  0 : <"bn128">
        %68 = felt.mul %4, %felt_const_0 : !felt.type<"bn128">, !felt.type<"bn128">
        %69 = felt.add %67, %68 : !felt.type<"bn128">, !felt.type<"bn128">
        constrain.eq %3, %69 : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_1_1 = felt.const  1 : <"bn128">
        %70 = felt.sub %felt_const_1_1, %2 : !felt.type<"bn128">, !felt.type<"bn128">
        %felt_const_2 = felt.const  2 : <"bn128">
        %71 = felt.mul %70, %felt_const_2 : !felt.type<"bn128">, !felt.type<"bn128">
        %72 = felt.mul %3, %2 : !felt.type<"bn128">, !felt.type<"bn128">
        %73 = felt.add %71, %72 : !felt.type<"bn128">, !felt.type<"bn128">
        constrain.eq %0, %73 : !felt.type<"bn128">, !felt.type<"bn128">
        %74 = pod.read %22[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        function.call @igualdadRepetida_4::@igualdadRepetida_4::@constrain(%21, %74) : (!struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>, !felt.type<"bn128">) -> () 
        %75 = pod.read %20[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        function.call @igualdadRepetida_2::@igualdadRepetida_2::@constrain(%19, %75) : (!struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>, !felt.type<"bn128">) -> () 
        %76 = pod.read %26[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        function.call @igualdadRepetida_3::@igualdadRepetida_3::@constrain(%25, %76) : (!struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>, !felt.type<"bn128">) -> () 
        %77 = pod.read %16[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        function.call @igualdadRepetida_3::@igualdadRepetida_3::@constrain(%15, %77) : (!struct.type<@igualdadRepetida_3::@igualdadRepetida_3<[]>>, !felt.type<"bn128">) -> () 
        %78 = pod.read %18[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        function.call @igualdadRepetida_4::@igualdadRepetida_4::@constrain(%17, %78) : (!struct.type<@igualdadRepetida_4::@igualdadRepetida_4<[]>>, !felt.type<"bn128">) -> () 
        %79 = pod.read %24[@in] : <[@in: !felt.type<"bn128">]>, !felt.type<"bn128">
        function.call @igualdadRepetida_2::@igualdadRepetida_2::@constrain(%23, %79) : (!struct.type<@igualdadRepetida_2::@igualdadRepetida_2<[]>>, !felt.type<"bn128">) -> () 
        function.return
      }
    }
  }
}
