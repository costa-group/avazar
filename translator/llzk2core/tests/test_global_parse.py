import pytest
from llzk_dialects.global_ import (GlobalDef, GlobalRead, GlobalWrite, _register_global_def,
                                   _global_core_name, _global_entry_core)
from llzk_dialects.core import SSAVar, GlobalVariable, Type, TranslationContext


class TestGlobal:

    # ── GlobalDef ─────────────────────────────────────────────────────────────

    def test_def_mutable(self):
        op = GlobalDef.parse("global.def @counter : !felt.type = 0")
        assert op.sym_name == GlobalVariable("@counter")
        assert op.type_ == Type("!felt.type")
        assert op.initial_value == "0"
        assert op.is_const is False

    def test_def_const(self):
        op = GlobalDef.parse("global.def const @PRIME : !felt.type = 17")
        assert op.is_const is True
        assert op.sym_name == GlobalVariable("@PRIME")

    def test_def_whitespace(self):
        op = GlobalDef.parse("  global.def @x : index = 0  ")
        assert op.sym_name == GlobalVariable("@x")

    def test_def_invalid(self):
        with pytest.raises(ValueError):
            GlobalDef.parse("global.def @x : !felt.type")  # missing = value

    def test_def_array_literal(self):
        line = (
            'global.def const @c : !array.type<3 x !felt.type<"bn128">> = '
            '[#felt<const 1 : <"bn128">> : !felt.type<"bn128">, '
            '#felt<const 2 : <"bn128">> : !felt.type<"bn128">, '
            '#felt<const 3 : <"bn128">> : !felt.type<"bn128">]'
        )
        op = GlobalDef.parse(line)
        assert op.sym_name == GlobalVariable("@c")
        assert op.initial_value == (
            '[#felt<const 1 : <"bn128">> : !felt.type<"bn128">, '
            '#felt<const 2 : <"bn128">> : !felt.type<"bn128">, '
            '#felt<const 3 : <"bn128">> : !felt.type<"bn128">]'
        )

    # ── Registration / GlobalRead.to_core ──────────────────────────────────────

    def test_register_scalar_value_not_in_globals_block(self):
        op = GlobalDef.parse("global.def const @PRIME : !felt.type = 17")
        ctx = TranslationContext()
        _register_global_def(op, ctx)
        assert list(op.to_core(ctx)) == []
        assert ctx.global2value["@PRIME"] == 17
        # Scalars are inlined at each read, never listed in `globals { }`.
        assert "@PRIME" not in ctx.global2core

    def test_register_array_literal_value_and_core_name(self):
        line = (
            'global.def const @c : !array.type<3 x !felt.type<"bn128">> = '
            '[#felt<const 1 : <"bn128">> : !felt.type<"bn128">, '
            '#felt<const 2 : <"bn128">> : !felt.type<"bn128">, '
            '#felt<const 3 : <"bn128">> : !felt.type<"bn128">]'
        )
        op = GlobalDef.parse(line)
        ctx = TranslationContext()
        _register_global_def(op, ctx)
        assert list(op.to_core(ctx)) == []
        assert ctx.global2value["@c"] == [1, 2, 3]
        assert ctx.global2core["@c"] == "@c"

    def test_register_nested_module_global_typed_literals(self):
        # The real nested-module literal shape (poseidon3_test_concrete.mlir).
        op = GlobalDef.parse(
            'global.def const @array_const_0 : !array.type<2 x !felt.type<"bn128">> = '
            '[ 7 : <"bn128">,  8 : <"bn128">]'
        )
        ctx = TranslationContext()
        _register_global_def(op, ctx, "@global")
        assert ctx.global2value["@global::@array_const_0"] == [7, 8]
        assert ctx.global2core["@global::@array_const_0"] == "@global_@array_const_0"

    def test_core_names_of_same_global_in_two_modules_differ(self):
        assert _global_core_name("@mod1::@arr") == "@mod1_@arr"
        assert _global_core_name("@mod2::@arr") == "@mod2_@arr"

    def test_global_entry_core_format(self):
        assert _global_entry_core("@global_@a", [1, 2, 3]) == "@global_@a: [1, 2, 3]"

    def test_read_to_core_scalar(self):
        def_op = GlobalDef.parse("global.def const @PRIME : !felt.type = 17")
        read_op = GlobalRead.parse("%v = global.read @PRIME : !felt.type")
        ctx = TranslationContext()
        _register_global_def(def_op, ctx)
        lines = list(read_op.to_core(ctx))
        assert lines == ["%v = 17"]
        assert ctx.var2const["%v"] == 17

    def test_read_to_core_array_copy_when_not_aliased(self):
        def_op = GlobalDef.parse(
            'global.def const @c : !array.type<3 x !felt.type<"bn128">> = [ 1 : <"bn128">, 2 : <"bn128">, 3 : <"bn128">]'
        )
        read_op = GlobalRead.parse(
            '%v = global.read const @global::@c : !array.type<3 x !felt.type<"bn128">>'
        )
        ctx = TranslationContext()
        _register_global_def(def_op, ctx, "@global")
        assert list(read_op.to_core(ctx)) == ["array.copy @global_@c %v"]

    def test_read_to_core_2d_array_copy(self):
        def_op = GlobalDef.parse(
            'global.def const @c : !array.type<2,2 x !felt.type<"bn128">> = '
            '[ 1 : <"bn128">, 2 : <"bn128">, 3 : <"bn128">, 4 : <"bn128">]'
        )
        read_op = GlobalRead.parse('%v = global.read @c : !array.type<2,2 x !felt.type<"bn128">>')
        ctx = TranslationContext()
        _register_global_def(def_op, ctx)
        assert ctx.global2value["@c"] == [1, 2, 3, 4]
        assert list(read_op.to_core(ctx)) == ["array.copy @c %v"]

    def test_read_to_core_aliased_emits_nothing(self):
        def_op = GlobalDef.parse(
            'global.def const @c : !array.type<2 x !felt.type<"bn128">> = [ 1 : <"bn128">, 2 : <"bn128">]'
        )
        read_op = GlobalRead.parse('%v = global.read @c : !array.type<2 x !felt.type<"bn128">>')
        ctx = TranslationContext()
        _register_global_def(def_op, ctx)
        read_op.aliased = True
        assert list(read_op.to_core(ctx)) == []

    # ── GlobalRead ────────────────────────────────────────────────────────────

    def test_read(self):
        op = GlobalRead.parse("%v = global.read @counter : !felt.type")
        assert op.result == SSAVar("%v")
        assert op.name_ref == GlobalVariable("@counter")
        assert op.result_type == Type("!felt.type")

    def test_read_whitespace(self):
        op = GlobalRead.parse("  %r = global.read @g : index  ")
        assert op.result == SSAVar("%r")

    def test_read_const(self):
        op = GlobalRead.parse(
            '%2 = global.read const @global::@array_const_0 : !array.type<72 x !felt.type<"bn128">>'
        )
        assert op.is_const
        assert op.name_ref == GlobalVariable("@global::@array_const_0")
        assert op.result_type == Type('!array.type<72 x !felt.type<"bn128">>')
        assert not GlobalRead.parse("%v = global.read @counter : !felt.type").is_const

    def test_read_missing_type(self):
        with pytest.raises(ValueError):
            GlobalRead.parse("%v = global.read @counter")

    def test_read_match(self):
        assert GlobalRead.match("%v = global.read @x : !felt.type") is True
        assert GlobalRead.match("global.write @x = %v : !felt.type") is False

    # ── GlobalWrite ───────────────────────────────────────────────────────────

    def test_write(self):
        op = GlobalWrite.parse("global.write @counter = %new_val : !felt.type")
        assert op.name_ref == GlobalVariable("@counter")
        assert op.value == SSAVar("%new_val")
        assert op.value_type == Type("!felt.type")

    def test_write_whitespace(self):
        op = GlobalWrite.parse("  global.write @g = %v : index  ")
        assert op.name_ref == GlobalVariable("@g")

    def test_write_invalid(self):
        with pytest.raises(ValueError):
            GlobalWrite.parse("global.write @x %v : !felt.type")  # missing =

    def test_write_match(self):
        assert GlobalWrite.match("global.write @x = %v : !felt.type") is True
        assert GlobalWrite.match("%v = global.read @x : !felt.type") is False
