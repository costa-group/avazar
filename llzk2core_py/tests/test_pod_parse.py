import pytest
from src.llzk_dialects.pod import PodNew, PodRead, PodWrite
from src.llzk_dialects.core import SSAVar, GlobalVariable, Type


class TestPod:

    # ── PodNew ────────────────────────────────────────────────────────────────

    def test_new_empty(self):
        op = PodNew.parse("%p = pod.new : !pod.type<[@x: !felt.type]>")
        assert op.result == SSAVar("%p")
        assert op.init_records == {}
        assert op.result_type == Type("!pod.type<[@x: !felt.type]>")

    def test_new_with_init(self):
        op = PodNew.parse("%p = pod.new {@x = %v0} : !pod.type<[@x: !felt.type]>")
        assert "@x" in op.init_records
        assert op.init_records["@x"] == SSAVar("%v0")

    def test_new_multi_init(self):
        op = PodNew.parse(
            "%p = pod.new {@x = %v0, @y = %v1} : !pod.type<[@x: !felt.type]>"
        )
        assert len(op.init_records) == 2

    def test_new_match(self):
        assert PodNew.match("%p = pod.new : !pod.type<[]>") is True
        assert PodNew.match("%p = pod.read %p [@x] : !t, !t") is False

    # ── PodRead ───────────────────────────────────────────────────────────────

    def test_read(self):
        op = PodRead.parse(
            "%v = pod.read %pod [@x] : !pod.type<[@x: !felt.type]>, !felt.type"
        )
        assert op.result == SSAVar("%v")
        assert op.pod_ref == SSAVar("%pod")
        assert op.record_name == GlobalVariable("@x")
        assert len(op.types) == 2

    def test_read_no_type(self):
        op = PodRead.parse("%v = pod.read %pod [@field]")
        assert op.types == []

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

    def test_write_no_type(self):
        op = PodWrite.parse("pod.write %pod [@x] = %v")
        assert op.types == []

    def test_write_match(self):
        assert PodWrite.match("pod.write %p [@x] = %v") is True
        assert PodWrite.match("%v = pod.read %p [@x]") is False
