import json
from atlas.aep.decision_rules import AEP, DEFAULT_PREDICATES, launch
from atlas.aep.claims_attrs_witnesses import prepare_claims_attrs_witness

Q = 10**6


class KernelOK:
    def eval(self, ctx):
        return {"ok": True}


def _run_seed(aep_toml_path: str, witness_path: str):
    W_in = json.load(open(witness_path, "r"))
    attrs, _, W = prepare_claims_attrs_witness(aep_toml_path, W_in, {"Q": Q})
    aep = AEP(C=list(attrs["claims"]), K=KernelOK(), W=W, theta={"Q": Q})
    d = launch(aep, DEFAULT_PREDICATES, attrs)
    return d


def test_unity_neutral_pass():
    d = _run_seed("examples/seeds/unity_neutral/aep.toml",
                  "examples/seeds/unity_neutral/witness_pass.json")
    assert d.status == "PASS" and d.code == 0


def test_unity_neutral_fail():
    d = _run_seed("examples/seeds/unity_neutral/aep.toml",
                  "examples/seeds/unity_neutral/witness_fail.json")
    assert d.status == "FAULT" and d.code == 2001


def test_mirror_safe_pass():
    d = _run_seed("examples/seeds/mirror_safe/aep.toml",
                  "examples/seeds/mirror_safe/witness_pass.json")
    assert d.status == "PASS"


def test_boundary_window_pass():
    d = _run_seed("examples/seeds/boundary_window/aep.toml",
                  "examples/seeds/boundary_window/witness_pass.json")
    assert d.status == "PASS"
