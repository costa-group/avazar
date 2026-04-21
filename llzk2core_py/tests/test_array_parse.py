import pytest
from llzk_dialects.array import ArrayNew, ArrayRead, ArrayWrite, ArrayExtract, ArrayInsert, ArrayLen
from llzk_dialects.core import SSAVar, Type


class TestArray:

    # ── ArrayNew ──────────────────────────────────────────────────────────────

    def test_new_empty(self):
        op = ArrayNew.parse("%a = array.new : !array.type<index>")
        assert op.result == SSAVar("%a")
        assert op.elements == []
        assert op.result_type == Type("!array.type<index>")

    def test_new_with_elements(self):
        op = ArrayNew.parse("%a = array.new : (%x, %y) : !array.type<index>")
        assert op.elements == [SSAVar("%x"), SSAVar("%y")]

    def test_new_single_element(self):
        op = ArrayNew.parse("%a = array.new : (%v) : !array.type<index>")
        assert len(op.elements) == 1

    def test_new_match(self):
        assert ArrayNew.match("%a = array.new : !array.type<index>") is True
        assert ArrayNew.match("%a = array.read %arr [%i] : !t, !t") is False

    # ── ArrayRead ─────────────────────────────────────────────────────────────

    def test_read(self):
        op = ArrayRead.parse("%v = array.read %arr [%i] : !array.type<index>, index")
        assert op.result == SSAVar("%v")
        assert op.arr_ref == SSAVar("%arr")
        assert op.indices == [SSAVar("%i")]
        assert op.types == [Type("!array.type<index>"), Type("index")]

    def test_read_multi_index(self):
        op = ArrayRead.parse("%v = array.read %m [%i, %j] : !array.type<index>, index")
        assert op.indices == [SSAVar("%i"), SSAVar("%j")]

    def test_read_no_type(self):
        op = ArrayRead.parse("%v = array.read %arr [%i]")
        assert op.types == []

    def test_read_invalid(self):
        with pytest.raises(ValueError):
            ArrayRead.parse("%v = array.read %arr : !type")  # missing brackets

    # ── ArrayWrite ────────────────────────────────────────────────────────────

    def test_write(self):
        op = ArrayWrite.parse(
            "array.write %arr [%i] = %val : !array.type<index>, index"
        )
        assert op.arr_ref == SSAVar("%arr")
        assert op.indices == [SSAVar("%i")]
        assert op.rvalue == SSAVar("%val")

    def test_write_no_type(self):
        op = ArrayWrite.parse("array.write %arr [%i] = %val")
        assert op.types == []

    def test_write_match(self):
        assert ArrayWrite.match("array.write %arr [%i] = %v") is True
        assert ArrayWrite.match("%v = array.read %arr [%i]") is False

    # ── ArrayExtract ──────────────────────────────────────────────────────────

    def test_extract(self):
        op = ArrayExtract.parse(
            "%sub = array.extract %mat [%i] : !array.type<index>"
        )
        assert op.result == SSAVar("%sub")
        assert op.arr_ref == SSAVar("%mat")
        assert op.indices == [SSAVar("%i")]
        assert op.arr_type == Type("!array.type<index>")

    def test_extract_match(self):
        assert ArrayExtract.match("%s = array.extract %m [%i] : !t") is True
        assert ArrayExtract.match("%s = array.insert %m [%i] = %v : !t") is False

    # ── ArrayInsert ───────────────────────────────────────────────────────────

    def test_insert(self):
        op = ArrayInsert.parse(
            "array.insert %mat [%i] = %row : !array.type<index>, !array.type<index>"
        )
        assert op.arr_ref == SSAVar("%mat")
        assert op.indices == [SSAVar("%i")]
        assert op.rvalue == SSAVar("%row")

    def test_insert_match(self):
        assert ArrayInsert.match("array.insert %m [%i] = %v") is True
        assert ArrayInsert.match("array.write %m [%i] = %v") is False

    # ── ArrayLen ──────────────────────────────────────────────────────────────

    def test_len(self):
        op = ArrayLen.parse("%n = array.len %arr, %dim : !array.type<index>")
        assert op.result == SSAVar("%n")
        assert op.arr_ref == SSAVar("%arr")
        assert op.dim == SSAVar("%dim")
        assert op.arr_type == Type("!array.type<index>")

    def test_len_invalid(self):
        with pytest.raises(ValueError):
            ArrayLen.parse("%n = array.len %arr : !array.type<index>")  # missing dim

    def test_len_match(self):
        assert ArrayLen.match("%n = array.len %a, %d : !t") is True
        assert ArrayLen.match("%v = array.read %a [%i]") is False
