import pytest
from llzk_dialects.poly import (
    PolyApplyMap, PolyReadConst, PolyUnifiableCast,
    PolyParam, PolyYield, PolyExpr, PolyTemplate, _register_pure_function,
)
from llzk_dialects.core import SSAVar, GlobalVariable, Type, TranslationContext
from llzk_dialects.felt import FeltConst
from llzk_dialects.function import FunctionDef, FunctionReturn, FunctionCall


class TestPoly:

    # ── PolyApplyMap ──────────────────────────────────────────────────────────

    def test_applymap(self):
        op = PolyApplyMap.parse(
            "%r = poly.applymap (%d0, %d1) [2] affine_map<(d0,d1)->(d0+d1)>"
        )
        assert op.result == SSAVar("%r")
        assert op.operands == [SSAVar("%d0"), SSAVar("%d1")]
        assert op.num_dims == 2
        assert "affine_map" in op.affine_map

    def test_applymap_single(self):
        op = PolyApplyMap.parse("%r = poly.applymap (%d0) [1] affine_map<(d0)->(d0)>")
        assert op.num_dims == 1
        assert len(op.operands) == 1

    def test_applymap_invalid(self):
        with pytest.raises(ValueError):
            PolyApplyMap.parse("%r = poly.applymap ()")  # missing num_dims and map

    def test_applymap_match(self):
        assert PolyApplyMap.match("%r = poly.applymap (%d) [1] affine_map<(d)->(d)>") is True
        assert PolyApplyMap.match("%r = poly.read_const @N : index") is False

    # ── PolyReadConst ─────────────────────────────────────────────────────────

    def test_read_const(self):
        op = PolyReadConst.parse("%n = poly.read_const @N : index")
        assert op.result == SSAVar("%n")
        assert op.const_name == GlobalVariable("@N")
        assert op.result_type == Type("index")

    def test_read_const_felt(self):
        op = PolyReadConst.parse("%p = poly.read_const @Prime : !felt.type")
        assert op.result_type == Type("!felt.type")

    def test_read_const_match(self):
        assert PolyReadConst.match("%n = poly.read_const @N : index") is True
        assert PolyReadConst.match("%r = poly.applymap (%d) [1] m") is False

    # ── PolyUnifiableCast ─────────────────────────────────────────────────────

    def test_unifiable_cast(self):
        op = PolyUnifiableCast.parse(
            "%r = poly.unifiable_cast %x : !felt.type -> !poly.tvar<@T>"
        )
        assert op.result == SSAVar("%r")
        assert op.input_val == SSAVar("%x")
        assert op.input_type == Type("!felt.type")
        assert op.result_type == Type("!poly.tvar<@T>")

    def test_unifiable_cast_match(self):
        assert PolyUnifiableCast.match("%r = poly.unifiable_cast %x : !t -> !s") is True
        assert PolyUnifiableCast.match("%r = poly.read_const @N : index") is False

    # ── PolyParam ─────────────────────────────────────────────────────────────

    def test_param_no_type(self):
        op = PolyParam.parse("poly.param @N")
        assert op.sym_name == GlobalVariable("@N")
        assert op.type_opt is None

    def test_param_with_type(self):
        op = PolyParam.parse("poly.param @T : !felt.type")
        assert op.type_opt == Type("!felt.type")

    def test_param_match(self):
        assert PolyParam.match("poly.param @N") is True
        assert PolyParam.match("poly.yield %v : index") is False

    # ── PolyYield ─────────────────────────────────────────────────────────────

    def test_yield(self):
        op = PolyYield.parse("poly.yield %v : index")
        assert op.value == SSAVar("%v")
        assert op.value_type == Type("index")

    def test_yield_felt(self):
        op = PolyYield.parse("  poly.yield %r : !felt.type  ")
        assert op.value_type == Type("!felt.type")

    def test_yield_missing_type(self):
        with pytest.raises(ValueError):
            PolyYield.parse("poly.yield %v")

    def test_yield_match(self):
        assert PolyYield.match("poly.yield %v : index") is True
        assert PolyYield.match("poly.param @N") is False

    # ── PolyExpr (BlockOperation) ─────────────────────────────────────────────

    def _parse_fn(self, start, end):
        ops = []
        for i in range(start, end):
            line = self.lines[i].strip()
            if not line or line == "}":
                continue
            if PolyYield.match(line):
                ops.append(PolyYield.parse(line))
        return ops

    def test_poly_expr(self):
        self.lines = [
            "poly.expr @e {",
            "poly.yield %v : index",
            "}",
        ]
        op, next_cur = PolyExpr.parse(self.lines, 0, self._parse_fn)
        assert op.sym_name == GlobalVariable("@e")
        assert len(op.body) == 1
        assert next_cur == 3

    def test_poly_expr_empty(self):
        self.lines = ["poly.expr @empty {", "}"]
        op, _ = PolyExpr.parse(self.lines, 0, self._parse_fn)
        assert op.body == []

    def test_poly_expr_match(self):
        assert PolyExpr.match("poly.expr @e {") is True
        assert PolyExpr.match("poly.template @T {") is False

    # ── PolyTemplate (BlockOperation) ─────────────────────────────────────────

    def _template_parse_fn(self, start, end):
        ops = []
        for i in range(start, end):
            line = self.lines[i].strip()
            if not line or line == "}":
                continue
            if PolyParam.match(line):
                ops.append(PolyParam.parse(line))
        return ops

    def test_poly_template(self):
        self.lines = [
            "poly.template @MyTemplate {",
            "poly.param @N",
            "poly.param @T : !felt.type",
            "}",
        ]
        op, next_cur = PolyTemplate.parse(self.lines, 0, self._template_parse_fn)
        assert op.sym_name == GlobalVariable("@MyTemplate")
        assert len(op.body) == 2
        assert next_cur == 4

    def test_poly_template_match(self):
        assert PolyTemplate.match("poly.template @T {") is True

    # ── PolyTemplate.to_core — pure function (no struct.def) ─────────────────

    def _inner_fn_body_parse(self, start, end):
        ops = []
        for i in range(start, end):
            line = self.lines[i].strip()
            if not line or line == "}":
                continue
            if FunctionReturn.match(line):
                ops.append(FunctionReturn.parse(line))
            elif FeltConst.match(line):
                ops.append(FeltConst.parse(line))
        return ops

    def _pure_function_template_parse_fn(self, start, end):
        ops = []
        for i in range(start, end):
            line = self.lines[i].strip()
            if not line or line == "}":
                continue
            if FunctionDef.match(line):
                op, _ = FunctionDef.parse(self.lines, i, self._inner_fn_body_parse)
                ops.append(op)
                break
        return ops

    def test_poly_template_to_core_pure_function(self):
        # A poly.template whose only child is a bare function.def (no
        # struct.def) — e.g. pointAdd_1 in escalarmulw4table_concrete.mlir —
        # registers and emits it directly, sourcing out-args from its own
        # function.return rather than struct.member declarations.
        self.lines = [
            "poly.template @pointAdd_1 {",
            "function.def @pointAdd_1(%arg0: !felt.type) -> !felt.type {",
            "%c = felt.const 1 : !felt.type",
            "function.return %c : !felt.type",
            "}",
            "}",
        ]
        op, _ = PolyTemplate.parse(self.lines, 0, self._pure_function_template_parse_fn)
        ctx = TranslationContext()
        out = ''.join(op.to_core(ctx))
        assert "def @pointAdd_1(%arg0: ff) -> %c: ff {" in out
        assert ctx.llzk_func2core["@pointAdd_1::@pointAdd_1"] == "@pointAdd_1"
        assert ctx.core_func2args["@pointAdd_1"][1] == [("%c", Type("!felt.type"))]
        # Cleared after emitting its body, mirroring StructDef.to_core.
        assert ctx.current_core_function is None

    def test_register_pure_function_idempotent(self):
        func = FunctionDef(
            GlobalVariable("@f"), "(%arg0: !felt.type) -> !felt.type",
            [FunctionReturn([SSAVar("%c")], [Type("!felt.type")])],
        )
        ctx = TranslationContext()
        _register_pure_function(func, "@f", ctx)
        first = dict(ctx.core_func2args)
        _register_pure_function(func, "@f", ctx)
        assert ctx.core_func2args == first

    def test_register_pure_function_requires_return_terminator(self):
        func = FunctionDef(GlobalVariable("@f"), "() -> !felt.type", [])
        ctx = TranslationContext()
        with pytest.raises(AssertionError):
            _register_pure_function(func, "@f", ctx)
        assert PolyTemplate.match("poly.expr @e {") is False
