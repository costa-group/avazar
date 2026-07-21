import pytest
from llzk_dialects.function import FunctionReturn, FunctionCall, FunctionDef
from llzk_dialects.core import SSAVar, GlobalVariable, Type, TranslationContext, LoopIndexedName
from llzk_dialects.felt import FeltConst, FeltBinary


class TestFunction:

    # ── FunctionReturn ────────────────────────────────────────────────────────

    def test_return_empty(self):
        op = FunctionReturn.parse("function.return")
        assert op.operands == []
        assert op.types == []

    def test_return_with_values(self):
        op = FunctionReturn.parse(
            "function.return %a, %b : !felt.type, !felt.type"
        )
        assert op.operands == [SSAVar("%a"), SSAVar("%b")]
        assert op.types == [Type("!felt.type"), Type("!felt.type")]

    def test_return_single(self):
        op = FunctionReturn.parse("  function.return %r : !felt.type  ")
        assert op.operands == [SSAVar("%r")]

    def test_return_match(self):
        assert FunctionReturn.match("function.return") is True
        assert FunctionReturn.match("function.call @f()") is False

    # ── FunctionCall ──────────────────────────────────────────────────────────

    def test_call_no_result(self):
        op = FunctionCall.parse("function.call @constrain(%self) : (!struct.type<@S>) -> ()")
        assert op.results == []
        assert op.callee == GlobalVariable("@constrain")
        assert op.args == [SSAVar("%self")]

    def test_call_with_result(self):
        op = FunctionCall.parse(
            "%r = function.call @compute(%self) : (!struct.type<@S>) -> (!felt.type)"
        )
        assert op.results == [SSAVar("%r")]
        assert op.callee == GlobalVariable("@compute")

    def test_call_no_args(self):
        op = FunctionCall.parse("function.call @init()")
        assert op.args == []

    def test_call_result_property_single(self):
        op = FunctionCall.parse("%r = function.call @f(%x)")
        assert op.result == SSAVar("%r")

    def test_call_result_property_no_result(self):
        op = FunctionCall.parse("function.call @f(%x)")
        assert op.result is None

    def test_call_member_hint_initially_none(self):
        op = FunctionCall.parse("%r = function.call @f(%x)")
        assert op._member_hint is None

    def test_call_match(self):
        assert FunctionCall.match("function.call @f(%x)") is True
        assert FunctionCall.match("function.return") is False

    # ── FunctionCall.to_core — LoopIndexedName resolution ────────────────────

    def _call_ctx(self):
        ctx = TranslationContext()
        ctx.llzk_func2core["@Sub"] = "Sub"
        ctx.core_func2args["Sub"] = ([], [("@out", Type("!felt.type"))])
        return ctx

    def test_call_to_core_loop_indexed_hint_not_unrolled(self):
        # _member_hint is a LoopIndexedName when the component array this
        # call feeds was read at a non-constant index (struct.py's
        # _annotate_array_component_reads). If the enclosing loop wasn't
        # unrolled (ctx.unroll_index is None), it resolves to the bare name.
        op = FunctionCall.parse("%r = function.call @Sub(%x)")
        op._member_hint = LoopIndexedName("last")
        ctx = self._call_ctx()
        lines = list(op.to_core(ctx))
        assert lines == ["call Sub(%x) to last.out"]
        assert ctx.ssa_to_name["%r_@out"] == "last.out"

    def test_call_to_core_loop_indexed_hint_unrolled(self):
        # SCFFor/SCFWhile.to_core sets ctx.unroll_index while translating
        # the current copy of a loop it unrolled (because the loop body
        # contains this very call) — the hint resolves to "last#2".
        op = FunctionCall.parse("%r = function.call @Sub(%x)")
        op._member_hint = LoopIndexedName("last")
        ctx = self._call_ctx()
        ctx.unroll_index = 2
        lines = list(op.to_core(ctx))
        assert lines == ["call Sub(%x) to last#2.out"]
        assert ctx.ssa_to_name["%r_@out"] == "last#2.out"

    # ── FunctionDef (BlockOperation) ─────────────────────────────────────────

    def _felt_parse_fn(self, start, end):
        ops = []
        for i in range(start, end):
            line = self.lines[i].strip()
            if not line or line == "}":
                continue
            if FunctionReturn.match(line):
                ops.append(FunctionReturn.parse(line))
            elif FeltBinary.match(line):
                ops.append(FeltBinary.parse(line))
            elif FeltConst.match(line):
                ops.append(FeltConst.parse(line))
        return ops

    def test_function_def_empty(self):
        self.lines = [
            "function.def @empty() {",
            "}",
        ]
        op, next_cur = FunctionDef.parse(self.lines, 0, self._felt_parse_fn)
        assert op.sym_name == GlobalVariable("@empty")
        assert op.body == []
        assert next_cur == 2

    def test_function_def_with_body(self):
        self.lines = [
            "function.def @add(%a: !felt.type, %b: !felt.type) -> (!felt.type) {",
            "%r = felt.add %a, %b",
            "function.return %r : !felt.type",
            "}",
        ]
        op, next_cur = FunctionDef.parse(self.lines, 0, self._felt_parse_fn)
        assert op.sym_name == GlobalVariable("@add")
        assert len(op.body) == 2
        assert next_cur == 4

    def test_function_def_match(self):
        assert FunctionDef.match("function.def @f(%x: !felt.type) {") is True
        assert FunctionDef.match("function.call @f(%x)") is False
