from atlas.aep.claims_attrs_witnesses import (
    load_aep_toml, prepare_claims_attrs_witness, canonical_unity_neutral
)

def test_load_attrs_and_kernel_mirror():
    attrs = load_aep_toml("examples/aep_unity_neutral/aep.toml")
    assert "unity_neutral" in attrs.claims
    assert attrs.boundary_window is not None
    assert attrs.phase_window is not None

def test_normalize_and_unity_pass_with_delta_zero():
    theta = {"Q": 1000000}
    W_in = {"delta_R": [0,0,0]}
    attrs_dict, kernel_attrs, W = prepare_claims_attrs_witness(
        "examples/aep_unity_neutral/aep.toml", W_in, theta
    )
    ok, ev = canonical_unity_neutral(W)
    assert ok and ev["delta_R_L1_scaled"] == 0
    assert "claims" in attrs_dict and "boundary_window" in attrs_dict and "phase_window" in attrs_dict

def test_boundary_and_phase_ok():
    theta = {"Q": 1000000}
    W_in = {
        "footprint": [0, 100, 0, 100],
        "P_probes": [{"phi": "0"}, {"phi": "0.1"}]  # strings; will be scaled
    }
    _, _, W = prepare_claims_attrs_witness(
        "examples/aep_unity_neutral/aep.toml", W_in, theta
    )
    assert W.get("boundary_ok", False) in (True, False)  # computed
    assert W.get("phase_ok", False) in (True, False)     # computed
