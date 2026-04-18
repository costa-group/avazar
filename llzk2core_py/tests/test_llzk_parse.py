import pytest
from llzk_dialects.llzk import LLZKNondet
from llzk_dialects.core import SSAVar, Type


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
