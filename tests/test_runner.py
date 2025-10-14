import numpy as np
from runner.metrics import spectral_bounds, neumann_tail_bound

F05 = 5 / 10
F07 = 7 / 10
F071 = 71 / 100
F1 = 1 / 1

def test_bounds_and_tail():
    K = np.diag([F05, F07])
    rho_hat, norm_hat = spectral_bounds(K)
    assert rho_hat < F1 and norm_hat <= F071
    tail = neumann_tail_bound(norm_hat, 3, F1)
    assert tail > 0
