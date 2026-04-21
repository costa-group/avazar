import pytest
from llzk_dialects.include import IncludeFrom
from llzk_dialects.core import GlobalVariable


class TestInclude:

    def test_include_from(self):
        op = IncludeFrom.parse('include.from "lib/math.llzk" as @Math')
        assert op.path == '"lib/math.llzk"'
        assert op.sym_name == GlobalVariable("@Math")

    def test_include_nested_path(self):
        op = IncludeFrom.parse('include.from "a/b/c.llzk" as @C')
        assert op.path == '"a/b/c.llzk"'

    def test_include_whitespace(self):
        op = IncludeFrom.parse('  include.from "x.llzk" as @X  ')
        assert op.sym_name == GlobalVariable("@X")

    def test_include_missing_as(self):
        with pytest.raises(ValueError):
            IncludeFrom.parse('include.from "x.llzk"')

    def test_include_match(self):
        assert IncludeFrom.match('include.from "x.llzk" as @X') is True
        assert IncludeFrom.match('global.def @x : !felt.type = 0') is False
