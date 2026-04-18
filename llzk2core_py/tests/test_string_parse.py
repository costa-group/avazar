import pytest
from llzk_dialects.string import StringNew
from llzk_dialects.core import SSAVar


class TestString:

    def test_string_new(self):
        op = StringNew.parse('%s = string.new "hello"')
        assert op.result == SSAVar("%s")
        assert op.value == '"hello"'

    def test_string_empty(self):
        op = StringNew.parse('%s = string.new ""')
        assert op.value == '""'

    def test_string_with_spaces(self):
        op = StringNew.parse('  %msg = string.new "hello world"  ')
        assert op.result == SSAVar("%msg")
        assert op.value == '"hello world"'

    def test_string_missing_quotes(self):
        with pytest.raises(ValueError):
            StringNew.parse("%s = string.new hello")

    def test_string_match(self):
        assert StringNew.match('%s = string.new "hi"') is True
        assert StringNew.match('%s = felt.const 1') is False
