import pytest
from llzk_dialects.array import ArrayNew, ArrayRead, ArrayWrite, ArrayExtract, ArrayInsert, ArrayLen
from llzk_dialects.core import SSAVar, Type, TranslationContext
from llzk_dialects.utils import array_felt_dimensions, array_felt_first_dimension


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


# ── array_felt_dimensions / array_felt_first_dimension ────────────────────────

class TestArrayFeltDimensions:

    # ── Real MLIR format: outer dims comma-separated, last dim uses 'x' ───────

    def test_1d_full_type(self):
        assert array_felt_dimensions("!array.type<4 x !felt.type<\"bn128\">>") == [4]

    def test_2d_full_type_comma(self):
        # Real MLIR format: <d0,d1 x elementType>
        assert array_felt_dimensions("!array.type<2,3 x !felt.type<\"bn128\">>") == [2, 3]

    def test_2d_full_type_comma_space(self):
        assert array_felt_dimensions("!array.type<2, 3 x !felt.type<\"bn128\">>") == [2, 3]

    def test_2d_square_comma(self):
        # Exactly the format from subcomponents_simple_concrete.mlir
        assert array_felt_dimensions("!array.type<2,2 x !felt.type<\"bn128\">>") == [2, 2]

    def test_3d_full_type_comma(self):
        assert array_felt_dimensions("!array.type<2,3,4 x !felt.type<\"bn128\">>") == [2, 3, 4]

    def test_1d_short_form(self):
        # Short form used inside array.read / array.write type annotations
        assert array_felt_dimensions("<16 x !felt.type<\"bn128\">>") == [16]

    def test_2d_short_form_comma(self):
        assert array_felt_dimensions("<2,2 x !felt.type<\"bn128\">>") == [2, 2]

    def test_non_felt_array(self):
        assert array_felt_dimensions("!array.type<index>") is None

    def test_felt_scalar(self):
        assert array_felt_dimensions("!felt.type<\"bn128\">") is None

    def test_first_dimension_1d(self):
        assert array_felt_first_dimension("!array.type<4 x !felt.type<\"bn128\">>") == 4

    def test_first_dimension_2d_is_product(self):
        assert array_felt_first_dimension("!array.type<2,3 x !felt.type<\"bn128\">>") == 6

    def test_first_dimension_3d_is_product(self):
        assert array_felt_first_dimension("!array.type<2,3,4 x !felt.type<\"bn128\">>") == 24

    def test_first_dimension_non_felt(self):
        assert array_felt_first_dimension("!array.type<index>") is None


# ── to_core ───────────────────────────────────────────────────────────────────

class TestArrayToCore:

    def _ctx(self, **var2const):
        ctx = TranslationContext()
        ctx.var2const.update(var2const)
        return ctx

    # ── Type.to_core ──────────────────────────────────────────────────────────

    def test_type_to_core_1d(self):
        assert Type("!array.type<4 x !felt.type<\"bn128\">>").to_core() == "arr<4>"

    def test_type_to_core_2d(self):
        assert Type("!array.type<2,3 x !felt.type<\"bn128\">>").to_core() == "arr<6>"

    def test_type_to_core_2d_square(self):
        # Real MLIR format from subcomponents_simple_concrete.mlir
        assert Type("!array.type<2,2 x !felt.type<\"bn128\">>").to_core() == "arr<4>"

    def test_type_to_core_3d(self):
        assert Type("!array.type<2,3,4 x !felt.type<\"bn128\">>").to_core() == "arr<24>"

    def test_type_to_core_felt(self):
        assert Type("!felt.type<\"bn128\">").to_core() == "ff"

    # ── ArrayNew.to_core ──────────────────────────────────────────────────────

    def test_new_to_core_1d(self):
        op = ArrayNew.parse("%a = array.new : !array.type<4 x !felt.type<\"bn128\">>")
        lines = list(op.to_core(self._ctx()))
        assert lines == ["array.new 4 %a"]

    def test_new_to_core_2d(self):
        op = ArrayNew.parse("%a = array.new : !array.type<2,3 x !felt.type<\"bn128\">>")
        lines = list(op.to_core(self._ctx()))
        assert lines == ["array.new 6 %a"]

    def test_new_to_core_2d_square(self):
        # Format from real MLIR (subcomponents_simple_concrete.mlir)
        op = ArrayNew.parse("%a = array.new : !array.type<2,2 x !felt.type<\"bn128\">>")
        lines = list(op.to_core(self._ctx()))
        assert lines == ["array.new 4 %a"]

    def test_new_to_core_3d(self):
        op = ArrayNew.parse("%a = array.new : !array.type<2,3,4 x !felt.type<\"bn128\">>")
        lines = list(op.to_core(self._ctx()))
        assert lines == ["array.new 24 %a"]

    # ── ArrayRead.to_core ─────────────────────────────────────────────────────

    def test_read_to_core_1d(self):
        op = ArrayRead.parse(
            "%v = array.read %arr [%i] : !array.type<4 x !felt.type<\"bn128\">>, !felt.type"
        )
        lines = list(op.to_core(self._ctx()))
        assert lines == ["array.read %arr[%i] %v"]

    def test_read_to_core_1d_no_type(self):
        op = ArrayRead.parse("%v = array.read %arr [%i]")
        lines = list(op.to_core(self._ctx()))
        assert lines == ["array.read %arr[%i] %v"]

    def test_read_to_core_2d_comma(self):
        # Real MLIR format: <d0,d1 x elementType>; dims=[3,4], strides=[4,1]
        op = ArrayRead.parse(
            "%v = array.read %arr [%i, %j]"
            " : <3,4 x !felt.type<\"bn128\">>, !felt.type<\"bn128\">"
        )
        lines = list(op.to_core(self._ctx()))
        assert lines == [
            "%v_s0 = 4",
            "%v_t0 = felt.mul %i %v_s0",
            "%v_t1 = %j",
            "%v_lin = felt.add %v_t0 %v_t1",
            "array.read %arr[%v_lin] %v",
        ]

    def test_read_to_core_2d_square(self):
        # Exactly the case from subcomponents_simple_concrete.mlir
        op = ArrayRead.parse(
            "%2 = array.read %arg0 [%0, %1] : <2,2 x !felt.type<\"bn128\">>, !felt.type<\"bn128\">"
        )
        lines = list(op.to_core(self._ctx()))
        assert lines == [
            "%2_s0 = 2",
            "%2_t0 = felt.mul %0 %2_s0",
            "%2_t1 = %1",
            "%2_lin = felt.add %2_t0 %2_t1",
            "array.read %arg0[%2_lin] %2",
        ]

    def test_read_to_core_2d_both_strides_one(self):
        # dims=[3,1], strides=[1,1] — both unit strides, no mul emitted
        op = ArrayRead.parse(
            "%v = array.read %arr [%i, %j]"
            " : <3,1 x !felt.type<\"bn128\">>, !felt.type<\"bn128\">"
        )
        lines = list(op.to_core(self._ctx()))
        assert lines == [
            "%v_t0 = %i",
            "%v_t1 = %j",
            "%v_lin = felt.add %v_t0 %v_t1",
            "array.read %arr[%v_lin] %v",
        ]

    def test_read_to_core_3d(self):
        # dims=[2,3,4], strides=[12,4,1]
        op = ArrayRead.parse(
            "%v = array.read %mat [%i, %j, %k]"
            " : <2,3,4 x !felt.type<\"bn128\">>, !felt.type<\"bn128\">"
        )
        lines = list(op.to_core(self._ctx()))
        assert lines == [
            "%v_s0 = 12",
            "%v_t0 = felt.mul %i %v_s0",
            "%v_s1 = 4",
            "%v_t1 = felt.mul %j %v_s1",
            "%v_acc1 = felt.add %v_t0 %v_t1",
            "%v_t2 = %k",
            "%v_lin = felt.add %v_acc1 %v_t2",
            "array.read %mat[%v_lin] %v",
        ]

    def test_read_to_core_2d_missing_type_raises(self):
        op = ArrayRead.parse("%v = array.read %arr [%i, %j]")  # no type annotation
        with pytest.raises(AssertionError):
            list(op.to_core(self._ctx()))

    # ── ArrayWrite.to_core ────────────────────────────────────────────────────

    def test_write_to_core_1d(self):
        op = ArrayWrite.parse(
            "array.write %arr [%i] = %val : !array.type<4 x !felt.type<\"bn128\">>, !felt.type"
        )
        lines = list(op.to_core(self._ctx()))
        assert lines == ["array.write %val %arr[%i]"]

    def test_write_to_core_2d(self):
        # Real MLIR format: <d0,d1 x elementType>; dims=[3,4]; base from rvalue %val
        op = ArrayWrite.parse(
            "array.write %arr [%i, %j] = %val"
            " : <3,4 x !felt.type<\"bn128\">>, !felt.type<\"bn128\">"
        )
        lines = list(op.to_core(self._ctx()))
        assert lines == [
            "%val_s0 = 4",
            "%val_t0 = felt.mul %i %val_s0",
            "%val_t1 = %j",
            "%val_lin = felt.add %val_t0 %val_t1",
            "array.write %val %arr[%val_lin]",
        ]

    def test_write_to_core_3d(self):
        # dims=[2,3,4], strides=[12,4,1]
        op = ArrayWrite.parse(
            "array.write %mat [%i, %j, %k] = %val"
            " : <2,3,4 x !felt.type<\"bn128\">>, !felt.type<\"bn128\">"
        )
        lines = list(op.to_core(self._ctx()))
        assert lines == [
            "%val_s0 = 12",
            "%val_t0 = felt.mul %i %val_s0",
            "%val_s1 = 4",
            "%val_t1 = felt.mul %j %val_s1",
            "%val_acc1 = felt.add %val_t0 %val_t1",
            "%val_t2 = %k",
            "%val_lin = felt.add %val_acc1 %val_t2",
            "array.write %val %mat[%val_lin]",
        ]

    def test_write_to_core_2d_missing_type_raises(self):
        op = ArrayWrite.parse("array.write %arr [%i, %j] = %val")
        with pytest.raises(AssertionError):
            list(op.to_core(self._ctx()))

    # ── ArrayLen.to_core ──────────────────────────────────────────────────────

    def test_len_to_core_dim0(self):
        op = ArrayLen.parse(
            "%n = array.len %arr, %d : !array.type<3,4 x !felt.type<\"bn128\">>"
        )
        ctx = self._ctx(**{"%d": 0})
        lines = list(op.to_core(ctx))
        assert lines == ["%n = 3"]
        assert ctx.var2const["%n"] == 3

    def test_len_to_core_dim1(self):
        op = ArrayLen.parse(
            "%n = array.len %arr, %d : !array.type<3,4 x !felt.type<\"bn128\">>"
        )
        ctx = self._ctx(**{"%d": 1})
        lines = list(op.to_core(ctx))
        assert lines == ["%n = 4"]
        assert ctx.var2const["%n"] == 4

    def test_len_to_core_1d(self):
        op = ArrayLen.parse(
            "%n = array.len %arr, %d : !array.type<7 x !felt.type<\"bn128\">>"
        )
        ctx = self._ctx(**{"%d": 0})
        lines = list(op.to_core(ctx))
        assert lines == ["%n = 7"]

    def test_len_to_core_unknown_dim_raises(self):
        op = ArrayLen.parse(
            "%n = array.len %arr, %d : !array.type<3 x 4 x !felt.type<\"bn128\">>"
        )
        with pytest.raises(AssertionError):
            list(op.to_core(self._ctx()))  # %d not in var2const

    def test_len_to_core_out_of_range_raises(self):
        op = ArrayLen.parse(
            "%n = array.len %arr, %d : !array.type<3 x 4 x !felt.type<\"bn128\">>"
        )
        ctx = self._ctx(**{"%d": 5})
        with pytest.raises(AssertionError):
            list(op.to_core(ctx))

    def test_len_to_core_non_felt_raises(self):
        op = ArrayLen.parse("%n = array.len %arr, %d : !array.type<index>")
        ctx = self._ctx(**{"%d": 0})
        with pytest.raises(AssertionError):
            list(op.to_core(ctx))
