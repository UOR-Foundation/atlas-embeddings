from multiplicity_core.ace import ACEProjector


def test_weighted_l1_projection_inside_ball():
    w_hat = {2: 0.1, 3: 0.2}
    b = {2: 0.4, 3: 0.3}
    R = 1.0
    w, gap = ACEProjector.project_weighted_l1(w_hat, b, R)
    assert w == w_hat
    assert gap >= 0


def test_weighted_l1_projection_active():
    w_hat = {2: 10.0, 3: 10.0}
    b = {2: 1.0, 3: 1.0}
    R = 1.0
    w, gap = ACEProjector.project_weighted_l1(w_hat, b, R)
    assert sum(abs(b[p] * w[p]) for p in w) <= R + 1e-9
    assert gap <= 1e-9
