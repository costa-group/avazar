import pytest
from src.llzk_dialects.scf import SCFYield, SCFCondition, SCFIf, SCFFor, SCFWhile
from src.llzk_dialects.core import SSAVar, Type
from src.llzk_dialects.felt import FeltConst, FeltBinary
from src.llzk_dialects.bool import BoolCmp
from src.llzk_dialects.constrain import ConstrainEq


class TestSCF:

    # ── SCFYield ──────────────────────────────────────────────────────────────

    def test_yield_empty(self):
        op = SCFYield.parse("scf.yield")
        assert op.operands == []
        assert op.types == []

    def test_yield_with_values(self):
        op = SCFYield.parse("scf.yield %a, %b : !felt.type, !felt.type")
        assert op.operands == [SSAVar("%a"), SSAVar("%b")]
        assert op.types == [Type("!felt.type"), Type("!felt.type")]

    def test_yield_single(self):
        op = SCFYield.parse("  scf.yield %r : index  ")
        assert op.operands == [SSAVar("%r")]

    def test_yield_match(self):
        assert SCFYield.match("scf.yield") is True
        assert SCFYield.match("scf.condition(%c)") is False

    # ── SCFCondition ──────────────────────────────────────────────────────────

    def test_condition_no_args(self):
        op = SCFCondition.parse("scf.condition(%cond)")
        assert op.condition == SSAVar("%cond")
        assert op.args == []

    def test_condition_with_args(self):
        op = SCFCondition.parse(
            "scf.condition(%ok) %a, %b : !felt.type, !felt.type"
        )
        assert op.condition == SSAVar("%ok")
        assert op.args == [SSAVar("%a"), SSAVar("%b")]

    def test_condition_match(self):
        assert SCFCondition.match("scf.condition(%c)") is True
        assert SCFCondition.match("scf.yield") is False

    # ── SCFIf (BlockOperation) ────────────────────────────────────────────────

    def _simple_parse_fn(self, start, end):
        ops = []
        for i in range(start, end):
            line = self.lines[i].strip()
            if not line or line in ("}", "} else {", "else {"):
                continue
            if SCFYield.match(line):
                ops.append(SCFYield.parse(line))
            elif FeltConst.match(line):
                ops.append(FeltConst.parse(line))
            elif ConstrainEq.match(line):
                ops.append(ConstrainEq.parse(line))
        return ops

    def test_if_no_else(self):
        self.lines = [
            "scf.if %cond {",
            "constrain.eq %a, %b",
            "}",
        ]
        op, next_cur = SCFIf.parse(self.lines, 0, self._simple_parse_fn)
        assert op.condition == SSAVar("%cond")
        assert len(op.then_body) == 1
        assert op.else_body is None
        assert next_cur == 3

    def test_if_with_else(self):
        self.lines = [
            "scf.if %cond {",
            "constrain.eq %a, %b",
            "} else {",
            "constrain.eq %c, %d",
            "}",
        ]
        op, next_cur = SCFIf.parse(self.lines, 0, self._simple_parse_fn)
        assert len(op.then_body) == 1
        assert op.else_body is not None
        assert len(op.else_body) == 1

    def test_if_with_results(self):
        self.lines = [
            "%r = scf.if %cond : !felt.type {",
            "scf.yield %a : !felt.type",
            "} else {",
            "scf.yield %b : !felt.type",
            "}",
        ]
        op, _ = SCFIf.parse(self.lines, 0, self._simple_parse_fn)
        assert op.results == [SSAVar("%r")]

    def test_if_match(self):
        assert SCFIf.match("scf.if %c {") is True
        assert SCFIf.match("scf.for %iv = %lb to %ub step %s {") is False

    # ── SCFFor (BlockOperation) ───────────────────────────────────────────────

    def test_for_basic(self):
        self.lines = [
            "scf.for %iv = %lb to %ub step %s {",
            "scf.yield",
            "}",
        ]
        op, next_cur = SCFFor.parse(self.lines, 0, self._simple_parse_fn)
        assert op.iv == SSAVar("%iv")
        assert op.lb == SSAVar("%lb")
        assert op.ub == SSAVar("%ub")
        assert op.step == SSAVar("%s")
        assert op.iter_args == []
        assert next_cur == 3

    def test_for_iter_args(self):
        self.lines = [
            "scf.for %iv = %lb to %ub step %s iter_args(%acc = %init) {",
            "scf.yield %acc : !felt.type",
            "}",
        ]
        op, _ = SCFFor.parse(self.lines, 0, self._simple_parse_fn)
        assert len(op.iter_args) == 1
        assert op.iter_args[0][0] == SSAVar("%acc")
        assert op.iter_args[0][1] == SSAVar("%init")

    def test_for_match(self):
        assert SCFFor.match("scf.for %iv = %lb to %ub step %s {") is True
        assert SCFFor.match("scf.while (%a = %b) {") is False

    # ── SCFWhile (BlockOperation) ─────────────────────────────────────────────

    def _while_parse_fn(self, start, end):
        ops = []
        for i in range(start, end):
            line = self.lines[i].strip()
            if not line or line in ("}", "do {"):
                continue
            if SCFYield.match(line):
                ops.append(SCFYield.parse(line))
            elif SCFCondition.match(line):
                ops.append(SCFCondition.parse(line))
        return ops

    def test_while_basic(self):
        self.lines = [
            "scf.while (%arg = %init) : (index) -> (index) {",
            "scf.condition(%cond) %arg",
            "}",
            "do {",
            "scf.yield %arg : index",
            "}",
        ]
        op, next_cur = SCFWhile.parse(self.lines, 0, self._while_parse_fn)
        assert op.init_args == [(SSAVar("%arg"), SSAVar("%init"))]
        assert len(op.before_body) == 1
        assert len(op.after_body) == 1
        assert next_cur == 6

    def test_while_match(self):
        assert SCFWhile.match("scf.while (%a = %b) {") is True
        assert SCFWhile.match("scf.if %c {") is False
