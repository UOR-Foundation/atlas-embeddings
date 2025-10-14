from atlas.runtime.backends import LocalBackend, run_multi_backend_and_compare
from atlas.aep.decision_rules import AEP


class KOK:
    def eval(self, ctx):
        return {"ok": True}


def test_same_inputs_identical_decisions_and_evidence():
    aep = AEP(
        C=[
            "unity_neutral",
            "mirror_safe",
            "boundary_window",
            "phase_window",
            "classes_mask",
        ],
        K=KOK(),
        W={
            "delta_R": [0, 0],
            "mirror_equal": True,
            "footprint": [0, 10, 0, 10],
            "phase_values": ["0", "0"],
            "classes_ok": True,
        },
        theta={"Q": 1_000_000},
    )
    attrs = {"claims": aep.C}
    be1 = LocalBackend(name="cpu", fixed_time_ns=123456789, device_tag="cpu")
    be2 = LocalBackend(name="gpu", fixed_time_ns=123456789, device_tag="gpu")
    out = run_multi_backend_and_compare(aep, attrs, [be1, be2])
    assert out["equal"] is True
    for item in out["results"]:
        dec = item["decision"]
        assert dec["status"] in ("PASS", "FAULT")
        assert all("ts" not in e for e in dec["log"])


def test_different_time_same_digest():
    aep = AEP(C=["unity_neutral"], K=KOK(), W={"delta_R": [0]}, theta={"Q": 1_000_000})
    attrs = {"claims": ["unity_neutral"]}
    beA = LocalBackend(name="cpuA", fixed_time_ns=111, device_tag="cpu")
    beB = LocalBackend(name="cpuB", fixed_time_ns=999_999_999_999, device_tag="cpu")
    out = run_multi_backend_and_compare(aep, attrs, [beA, beB])
    assert out["equal"] is True
