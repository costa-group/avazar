import pytest
from llzk_dialects.parser import LLZKParser
from llzk_dialects.llzk import ModuleOp
from llzk_dialects.felt import FeltConst, FeltDialect
from llzk_dialects.constrain import ConstrainEq, ConstrainDialect
from llzk_dialects.struct import StructMember, StructDef, StructDialect
from llzk_dialects.function import FunctionDef, FunctionDialect
from llzk_dialects.scf import SCFYield, SCFIf, SCFDialect
from llzk_dialects.core import SSAVar, GlobalVariable, Type


def make_parser(lines):
    p = LLZKParser(lines)
    p.add_dialects([
        FeltDialect(),
        ConstrainDialect(),
        StructDialect(),
        FunctionDialect(),
        SCFDialect(),
    ])
    return p


class TestLLZKParser:

    def test_empty_input(self):
        ops = make_parser([]).parse()
        assert ops == []

    def test_empty_lines_only(self):
        ops = make_parser(["", "   ", "\t"]).parse()
        assert ops == []

    # ── Flat op at top level ──────────────────────────────────────────────────

    def test_single_flat_op(self):
        ops = make_parser(["%c = felt.const 7"]).parse()
        assert len(ops) == 1
        assert isinstance(ops[0], FeltConst)
        assert ops[0].result == SSAVar("%c")
        assert ops[0].constant == 7

    def test_multiple_flat_ops(self):
        ops = make_parser([
            "%a = felt.const 1",
            "%b = felt.const 2",
            "constrain.eq %a, %b",
        ]).parse()
        assert len(ops) == 3
        assert isinstance(ops[0], FeltConst)
        assert isinstance(ops[1], FeltConst)
        assert isinstance(ops[2], ConstrainEq)

    # ── Unknown prefix silently skipped ──────────────────────────────────────

    def test_unknown_prefix_raises(self):
        with pytest.raises(ValueError, match="no operation matches"):
            make_parser(["unknown.op %x"]).parse()

    def test_structural_markers_skipped(self):
        ops = make_parser([
            "}",
            "} else {",
            "do {",
            "^bb0:",
            "%c = felt.const 3",
        ]).parse()
        assert len(ops) == 1
        assert isinstance(ops[0], FeltConst)

    # ── Module wrapper ────────────────────────────────────────────────────────

    def test_module_wrapper(self):
        ops = make_parser([
            "module {",
            "  %c = felt.const 10",
            "}",
        ]).parse()
        assert len(ops) == 1
        assert isinstance(ops[0], ModuleOp)
        assert ops[0].lang is False
        assert ops[0].main_type is None
        assert len(ops[0].body) == 1
        assert isinstance(ops[0].body[0], FeltConst)

    def test_module_attributes_lang_and_main(self):
        ops = make_parser([
            "module attributes {llzk.lang, llzk.main = !struct.type<@S::@S<[]>>} {",
            "  %c = felt.const 99",
            "}",
        ]).parse()
        assert len(ops) == 1
        m = ops[0]
        assert isinstance(m, ModuleOp)
        assert m.lang is True
        assert m.main_type == Type("!struct.type<@S::@S<[]>>")
        assert m.body[0].constant == 99

    def test_module_lang_only(self):
        ops = make_parser([
            "module attributes {llzk.lang} {",
            "  %c = felt.const 1",
            "}",
        ]).parse()
        m = ops[0]
        assert m.lang is True
        assert m.main_type is None

    # ── Block op (struct.def) ─────────────────────────────────────────────────

    def test_struct_def_with_member(self):
        ops = make_parser([
            "struct.def @Foo {",
            "  struct.member @x : !felt.type",
            "}",
        ]).parse()
        assert len(ops) == 1
        assert isinstance(ops[0], StructDef)
        assert ops[0].sym_name == GlobalVariable("@Foo")
        assert len(ops[0].body) == 1
        assert isinstance(ops[0].body[0], StructMember)

    def test_struct_def_with_function_body(self):
        ops = make_parser([
            "struct.def @Bar {",
            "  struct.member @v : !felt.type",
            "  function.def @constrain(%self: !struct.type<@Bar>) {",
            "    constrain.eq %a, %b",
            "  }",
            "}",
        ]).parse()
        assert isinstance(ops[0], StructDef)
        assert len(ops[0].body) == 2
        assert isinstance(ops[0].body[1], FunctionDef)
        fn = ops[0].body[1]
        assert len(fn.body) == 1
        assert isinstance(fn.body[0], ConstrainEq)

    # ── Nested block op (scf.if inside function) ──────────────────────────────

    def test_scf_if_inside_function(self):
        ops = make_parser([
            "function.def @check(%c: i1) {",
            "  scf.if %c {",
            "    constrain.eq %a, %b",
            "  } else {",
            "    constrain.eq %x, %y",
            "  }",
            "}",
        ]).parse()
        assert len(ops) == 1
        fn = ops[0]
        assert isinstance(fn, FunctionDef)
        assert len(fn.body) == 1
        scf = fn.body[0]
        assert isinstance(scf, SCFIf)
        assert len(scf.then_body) == 1
        assert scf.else_body is not None
        assert len(scf.else_body) == 1

    # ── Module wrapper with nested block op ──────────────────────────────────

    def test_module_with_struct(self):
        ops = make_parser([
            "module {",
            "  struct.def @S {",
            "    struct.member @f : !felt.type",
            "  }",
            "}",
        ]).parse()
        assert len(ops) == 1
        assert isinstance(ops[0], ModuleOp)
        assert isinstance(ops[0].body[0], StructDef)
