import pytest
from llzk_dialects.poly import (
    PolyApplyMap, PolyReadConst, PolyUnifiableCast,
    PolyParam, PolyYield, PolyExpr, PolyTemplate,
)
from llzk_dialects.core import SSAVar, GlobalVariable, Type
from llzk_dialects.felt import FeltConst


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
        assert PolyTemplate.match("poly.expr @e {") is False
