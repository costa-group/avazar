module attributes {llzk.lang, llzk.main = !struct.type<@IsZero_0::@IsZero_0<[]>>} {
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
}
