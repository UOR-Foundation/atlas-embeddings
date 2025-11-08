from multiplicity_core.runtime import MultiplicityRuntime
from multiplicity_core.ace import ACEParams


def test_runtime_ingest_and_switch():
    rt = MultiplicityRuntime(active_class="1A")
    rt.toggles.set_schedule(3, [True, False])  # gate lane 3 on even t only
    out0 = rt.ingest(0, {3: 1.0, 4: 2.0})
    assert 3 in out0 and 4 in out0
    out1 = rt.ingest(1, {3: 1.0, 4: 2.0})
    assert 3 not in out1 and 4 in out1
    # ACE projection is callable
    w = rt.ace_project({2: 0.7, 3: 0.8}, {2: 0.5, 3: 0.5}, ACEParams(X_t=0.1, eps_t=0.1))
    assert isinstance(w, dict)
    # Class switch keeps isolation
    rt.switch_class("2B")
    out2 = rt.read_lanes([3, 4])
    assert out2[3] == 0 and out2[4] == 0
