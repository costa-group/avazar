import pytest
from src.llzk_dialects.function import FunctionReturn, FunctionCall, FunctionDef
from src.llzk_dialects.core import SSAVar, GlobalVariable, Type
from src.llzk_dialects.felt import FeltConst, FeltBinary


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

    def test_call_match(self):
        assert FunctionCall.match("function.call @f(%x)") is True
        assert FunctionCall.match("function.return") is False

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
