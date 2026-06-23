import pytest
from llzk_dialects.pod import PodNew, PodRead, PodWrite
from llzk_dialects.core import SSAVar, GlobalVariable, Type, TranslationContext


class TestPod:

    # ── PodNew ────────────────────────────────────────────────────────────────

    def test_new_empty(self):
        op = PodNew.parse("%p = pod.new : !pod.type<[@x: !felt.type]>")
        assert op.result == SSAVar("%p")
        assert op.init_records == {}
        assert op.result_type == {"@x": Type("!felt.type")}

    def test_new_with_init(self):
        op = PodNew.parse("%p = pod.new {@x = %v0} : !pod.type<[@x: !felt.type]>")
        assert "@x" in op.init_records
        assert op.init_records["@x"] == SSAVar("%v0")

    def test_new_multi_init(self):
        op = PodNew.parse(
            "%p = pod.new {@x = %v0, @y = %v1} : !pod.type<[@x: !felt.type]>"
        )
        assert len(op.init_records) == 2

    def test_new_init_complex_type(self):
        # Init records contain '=' signs — match() must not split on them.
        line = ('%pod = pod.new { @count = %c2 }  : '
                '!pod.type<[@count: index, @comp: !struct.type<@S<[]>>, @params: !pod.type<[]>]>')
        op = PodNew.parse(line)
        assert op.result == SSAVar("%pod")
        assert "@count" in op.init_records
        assert op.init_records["@count"] == SSAVar("%c2")
        assert "@count" in op.result_type
        assert "@comp" in op.result_type
        assert "@params" in op.result_type
        assert op.result_type["@count"] == Type("index")
        assert op.result_type["@comp"] == Type("!struct.type<@S<[]>>")
        assert op.result_type["@params"] == Type("!pod.type<[]>")

    def test_new_empty_pod_type(self):
        op = PodNew.parse("%p = pod.new : !pod.type<[]>")
        assert op.result_type == {}

    def test_new_match(self):
        assert PodNew.match("%p = pod.new : !pod.type<[]>") is True
        assert PodNew.match("%p = pod.read %p [@x] : !t, !t") is False
        # Match must work even when init records introduce extra '=' signs.
        assert PodNew.match("%p = pod.new { @x = %v } : !pod.type<[]>") is True

    # ── PodRead ───────────────────────────────────────────────────────────────

    def test_read(self):
        op = PodRead.parse(
            "%v = pod.read %pod [@x] : !pod.type<[@x: !felt.type]>, !felt.type"
        )
        assert op.result == SSAVar("%v")
        assert op.pod_ref == SSAVar("%pod")
        assert op.record_name == GlobalVariable("@x")
        assert op.pod_type == {"@x": Type("!felt.type")}
        assert op.result_type == Type("!felt.type")

    def test_read_no_type(self):
        op = PodRead.parse("%v = pod.read %pod [@field]")
        assert op.pod_type == {}
        assert op.result_type is None

    def test_read_complex_pod_type(self):
        line = ("%v = pod.read %p [@comp] : "
                "!pod.type<[@count: index, @comp: !struct.type<@S<[]>>, @params: !pod.type<[]>]>, "
                "!struct.type<@S<[]>>")
        op = PodRead.parse(line)
        assert "@count" in op.pod_type
        assert "@comp" in op.pod_type
        assert "@params" in op.pod_type
        assert op.result_type == Type("!struct.type<@S<[]>>")

    def test_read_match(self):
        assert PodRead.match("%v = pod.read %p [@x]") is True
        assert PodRead.match("pod.write %p [@x] = %v") is False

    # ── PodWrite ──────────────────────────────────────────────────────────────

    def test_write(self):
        op = PodWrite.parse(
            "pod.write %pod [@x] = %val : !pod.type<[@x: !felt.type]>, !felt.type"
        )
        assert op.pod_ref == SSAVar("%pod")
        assert op.record_name == GlobalVariable("@x")
        assert op.value == SSAVar("%val")
        assert op.pod_type == {"@x": Type("!felt.type")}
        assert op.value_type == Type("!felt.type")

    def test_write_no_type(self):
        op = PodWrite.parse("pod.write %pod [@x] = %v")
        assert op.pod_type == {}
        assert op.value_type is None

    def test_write_complex_pod_type(self):
        line = ("pod.write %p [@count] = %c : "
                "!pod.type<[@count: index, @comp: !struct.type<@S<[]>>, @params: !pod.type<[]>]>, "
                "index")
        op = PodWrite.parse(line)
        assert "@count" in op.pod_type
        assert "@comp" in op.pod_type
        assert op.value_type == Type("index")

    def test_write_match(self):
        assert PodWrite.match("pod.write %p [@x] = %v") is True
        assert PodWrite.match("%v = pod.read %p [@x]") is False


# ── to_core ───────────────────────────────────────────────────────────────────

class TestPodToCore:
    """
    Tests for the pod-in-pod assignment fix:
      - is_ff no longer treats !pod.type as a scalar
      - empty-string yields are filtered in PodNew/PodRead/PodWrite.to_core()
    """

    def _ctx(self):
        return TranslationContext()

    # ── PodNew — scalar init ──────────────────────────────────────────────────

    def test_new_scalar_init_yields_assignment(self):
        ctx = self._ctx()
        op = PodNew.parse("%p = pod.new {@x = %v} : !pod.type<[@x: !felt.type]>")
        lines = list(op.to_core(ctx))
        assert lines == ["%p_@x = %v"]

    def test_new_registers_storage_var(self):
        ctx = self._ctx()
        op = PodNew.parse("%p = pod.new : !pod.type<[@x: !felt.type]>")
        list(op.to_core(ctx))
        assert "%p" in ctx.ssa2pod_var
        assert ctx.ssa2pod_var["%p"]["@x"][0] == "%p_@x"

    # ── PodNew — pod-typed field init (the fix) ───────────────────────────────

    def test_new_empty_pod_field_yields_nothing(self):
        ctx = self._ctx()
        ctx.ssa2pod_var["%sub"] = {}
        op = PodNew.parse(
            "%p = pod.new {@f = %sub} : !pod.type<[@f: !pod.type<[]>]>"
        )
        lines = list(op.to_core(ctx))
        assert lines == []

    def test_new_empty_pod_field_registers_storage_as_pod(self):
        ctx = self._ctx()
        ctx.ssa2pod_var["%sub"] = {}
        op = PodNew.parse(
            "%p = pod.new {@f = %sub} : !pod.type<[@f: !pod.type<[]>]>"
        )
        list(op.to_core(ctx))
        assert ctx.ssa2pod_var.get("%p_@f") == {}

    # ── PodRead — scalar field ────────────────────────────────────────────────

    def test_read_scalar_yields_assignment(self):
        ctx = self._ctx()
        ctx.ssa2pod_var["%pod"] = {"@x": ("%pod_@x", Type("!felt.type"))}
        op = PodRead.parse("%v = pod.read %pod [@x] : !pod.type<[@x: !felt.type]>, !felt.type")
        lines = list(op.to_core(ctx))
        assert lines == ["%v = %pod_@x"]

    # ── PodRead — pod-typed field (the fix) ───────────────────────────────────

    def test_read_empty_pod_field_yields_nothing(self):
        ctx = self._ctx()
        ctx.ssa2pod_var["%pod_0"] = {"@params": ("%pod_0_@params", Type("!pod.type<[]>"))}
        ctx.ssa2pod_var["%pod_0_@params"] = {}
        op = PodRead.parse(
            "%13 = pod.read %pod_0 [@params] : "
            "!pod.type<[@params: !pod.type<[]>]>, !pod.type<[]>"
        )
        lines = list(op.to_core(ctx))
        assert lines == []

    def test_read_empty_pod_field_registers_result_as_pod(self):
        ctx = self._ctx()
        ctx.ssa2pod_var["%pod_0"] = {"@params": ("%pod_0_@params", Type("!pod.type<[]>"))}
        ctx.ssa2pod_var["%pod_0_@params"] = {}
        op = PodRead.parse(
            "%13 = pod.read %pod_0 [@params] : "
            "!pod.type<[@params: !pod.type<[]>]>, !pod.type<[]>"
        )
        list(op.to_core(ctx))
        assert ctx.ssa2pod_var.get("%13") == {}

    # ── PodWrite — scalar field ───────────────────────────────────────────────

    def test_write_scalar_yields_assignment(self):
        ctx = self._ctx()
        ctx.ssa2pod_var["%pod"] = {"@x": ("%pod_@x", Type("!felt.type"))}
        op = PodWrite.parse("pod.write %pod [@x] = %v : !pod.type<[@x: !felt.type]>, !felt.type")
        lines = list(op.to_core(ctx))
        assert lines == ["%pod_@x = %v"]

    # ── PodWrite — pod-typed field (the fix) ──────────────────────────────────

    def test_write_empty_pod_field_yields_nothing(self):
        ctx = self._ctx()
        ctx.ssa2pod_var["%pod_0"] = {"@params": ("%pod_0_@params", Type("!pod.type<[]>"))}
        ctx.ssa2pod_var["%pod_0_@params"] = {}
        ctx.ssa2pod_var["%new_pod"] = {}
        op = PodWrite.parse(
            "pod.write %pod_0 [@params] = %new_pod : "
            "!pod.type<[@params: !pod.type<[]>]>, !pod.type<[]>"
        )
        lines = list(op.to_core(ctx))
        assert lines == []

    # ── Full chain: new → new (pod field) → read (the fix scenario) ──────────

    def test_pod_in_pod_chain_propagates_empty_mapping(self):
        # Mirrors the IsEqual_1 @compute pattern from subcomponents_simple_concrete.mlir:
        #   %pod = pod.new : <[]>
        #   %pod_0 = pod.new { @params = %pod } : <[@params: !pod.type<[]>]>
        #   %13 = pod.read %pod_0[@params] : ..., !pod.type<[]>
        ctx = self._ctx()

        empty_pod = PodNew.parse("%pod = pod.new : !pod.type<[]>")
        list(empty_pod.to_core(ctx))
        assert ctx.ssa2pod_var["%pod"] == {}

        pod_0 = PodNew.parse(
            "%pod_0 = pod.new {@params = %pod} : !pod.type<[@params: !pod.type<[]>]>"
        )
        list(pod_0.to_core(ctx))
        assert ctx.ssa2pod_var.get("%pod_0_@params") == {}

        read = PodRead.parse(
            "%13 = pod.read %pod_0 [@params] : "
            "!pod.type<[@params: !pod.type<[]>]>, !pod.type<[]>"
        )
        lines = list(read.to_core(ctx))
        assert lines == []
        assert ctx.ssa2pod_var.get("%13") == {}
