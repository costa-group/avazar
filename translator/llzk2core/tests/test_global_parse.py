import pytest
from llzk_dialects.global_ import GlobalDef, GlobalRead, GlobalWrite
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

    # ── GlobalDef.to_core / GlobalRead.to_core ─────────────────────────────────

    def test_def_to_core_scalar_registers_value(self):
        op = GlobalDef.parse("global.def const @PRIME : !felt.type = 17")
        ctx = TranslationContext()
        assert list(op.to_core(ctx)) == []
        assert ctx.global2value["@PRIME"] == 17

    def test_def_to_core_array_literal_registers_value(self):
        line = (
            'global.def const @c : !array.type<3 x !felt.type<"bn128">> = '
            '[#felt<const 1 : <"bn128">> : !felt.type<"bn128">, '
            '#felt<const 2 : <"bn128">> : !felt.type<"bn128">, '
            '#felt<const 3 : <"bn128">> : !felt.type<"bn128">]'
        )
        op = GlobalDef.parse(line)
        ctx = TranslationContext()
        assert list(op.to_core(ctx)) == []
        assert ctx.global2value["@c"] == [1, 2, 3]

    def test_read_to_core_scalar(self):
        def_op = GlobalDef.parse("global.def const @PRIME : !felt.type = 17")
        read_op = GlobalRead.parse("%v = global.read @PRIME : !felt.type")
        ctx = TranslationContext()
        list(def_op.to_core(ctx))
        lines = list(read_op.to_core(ctx))
        assert lines == ["%v = 17"]
        assert ctx.var2const["%v"] == 17

    def test_read_to_core_1d_array(self):
        line = (
            'global.def const @c : !array.type<3 x !felt.type<"bn128">> = '
            '[#felt<const 1 : <"bn128">> : !felt.type<"bn128">, '
            '#felt<const 2 : <"bn128">> : !felt.type<"bn128">, '
            '#felt<const 3 : <"bn128">> : !felt.type<"bn128">]'
        )
        def_op = GlobalDef.parse(line)
        read_op = GlobalRead.parse(
            '%v = global.read @c : !array.type<3 x !felt.type<"bn128">>'
        )
        ctx = TranslationContext()
        list(def_op.to_core(ctx))
        lines = list(read_op.to_core(ctx))
        assert lines == [
            "array.new 3 %v",
            "array.write 1 %v[0]",
            "array.write 2 %v[1]",
            "array.write 3 %v[2]",
        ]

    def test_read_to_core_2d_array_uses_total_size(self):
        line = (
            'global.def const @c : !array.type<2,2 x !felt.type<"bn128">> = '
            '[#felt<const 1 : <"bn128">> : !felt.type<"bn128">, '
            '#felt<const 2 : <"bn128">> : !felt.type<"bn128">, '
            '#felt<const 3 : <"bn128">> : !felt.type<"bn128">, '
            '#felt<const 4 : <"bn128">> : !felt.type<"bn128">]'
        )
        def_op = GlobalDef.parse(line)
        read_op = GlobalRead.parse(
            '%v = global.read @c : !array.type<2,2 x !felt.type<"bn128">>'
        )
        ctx = TranslationContext()
        list(def_op.to_core(ctx))
        lines = list(read_op.to_core(ctx))
        assert lines == [
            "array.new 4 %v",
            "array.write 1 %v[0]",
            "array.write 2 %v[1]",
            "array.write 3 %v[2]",
            "array.write 4 %v[3]",
        ]

    # ── GlobalRead ────────────────────────────────────────────────────────────

    def test_read(self):
        op = GlobalRead.parse("%v = global.read @counter : !felt.type")
        assert op.result == SSAVar("%v")
        assert op.name_ref == GlobalVariable("@counter")
        assert op.result_type == Type("!felt.type")

    def test_read_whitespace(self):
        op = GlobalRead.parse("  %r = global.read @g : index  ")
        assert op.result == SSAVar("%r")

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
