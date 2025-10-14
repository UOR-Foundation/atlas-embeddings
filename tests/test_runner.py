import numpy as np
from runner.metrics import spectral_bounds, neumann_tail_bound

def test_bounds_and_tail():
    K = np.diag([0.5, 0.7])
    rho_hat, norm_hat = spectral_bounds(K)
    assert rho_hat < 1 and norm_hat <= 0.71
    tail = neumann_tail_bound(norm_hat, 3, 1.0)
    assert tail > 0
