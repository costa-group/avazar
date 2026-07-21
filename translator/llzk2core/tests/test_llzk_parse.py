import pytest
from llzk_dialects.llzk import LLZKNondet, ModuleOp
from llzk_dialects.core import SSAVar, Type, GlobalVariable, TranslationContext
from llzk_dialects.poly import PolyTemplate
from llzk_dialects.function import FunctionDef, FunctionReturn, FunctionCall


class TestLLZK:

    def test_nondet(self):
        op = LLZKNondet.parse("%x = llzk.nondet : !felt.type")
        assert op.result == SSAVar("%x")
        assert op.result_type == Type("!felt.type")

    def test_nondet_whitespace(self):
        op = LLZKNondet.parse("  %v = llzk.nondet : !array.type<index>  ")
        assert op.result == SSAVar("%v")
        assert op.result_type == Type("!array.type<index>")

    def test_nondet_missing_type(self):
        with pytest.raises(ValueError):
            LLZKNondet.parse("%x = llzk.nondet")

    def test_nondet_match(self):
        assert LLZKNondet.match("%x = llzk.nondet : !felt.type") is True
        assert LLZKNondet.match("%x = felt.const 1") is False

    # ── ModuleOp.to_core — pure-function forward-reference pre-pass ─────────

    def test_module_prepass_registers_forward_referenced_pure_function(self):
        # A pure function template may be declared textually *after* a
        # caller that references it (e.g. escalarmulw4table_concrete.mlir's
        # EscalarMulW4Table_0, declared first, calls pointAdd_1, declared
        # afterwards) — unlike struct-to-struct calls, which this codebase
        # already requires to be declared before their callers. ModuleOp's
        # pre-pass registers every pure function's signature before any body
        # is translated, so this works regardless of declaration order.
        call = FunctionCall([SSAVar("%r")], GlobalVariable("@Callee::@Callee"), [SSAVar("%x")], None)
        caller_func = FunctionDef(
            GlobalVariable("@Caller"), "(%x: !felt.type) -> !felt.type",
            [call, FunctionReturn([SSAVar("%r")], [Type("!felt.type")])],
        )
        callee_func = FunctionDef(
            GlobalVariable("@Callee"), "(%arg0: !felt.type) -> !felt.type",
            [FunctionReturn([SSAVar("%arg0")], [Type("!felt.type")])],
        )
        # Caller declared (and listed) before its callee, on purpose.
        caller_template = PolyTemplate(GlobalVariable("@Caller"), [caller_func])
        callee_template = PolyTemplate(GlobalVariable("@Callee"), [callee_func])

        module = ModuleOp(lang=True, main_type=None, body=[caller_template, callee_template])
        ctx = TranslationContext()
        gen = module.to_core(ctx)
        next(gen)  # the pre-pass runs synchronously, before the first yield
        assert ctx.llzk_func2core["@Callee::@Callee"] == "@Callee"
        assert ctx.llzk_func2core["@Caller::@Caller"] == "@Caller"
