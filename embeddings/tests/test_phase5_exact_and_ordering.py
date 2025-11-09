from core.arithmetic import Q as _Q, is_Q
from e8.roots import generate_e8_roots, dot
from e8.order import iota_key


def test_all_roots_exact_and_sorted_by_iota():
    R1 = generate_e8_roots()
    # exact type
    assert len(R1) == 240
    assert all(is_Q(x) for v in R1 for x in v)
    # deterministic order: regenerate and compare
    R2 = generate_e8_roots()
    assert R1 == R2
    # stable key monotonicity
    K = [iota_key(v) for v in R1]
    assert K == sorted(K)


def test_inner_products_are_rational():
    R = generate_e8_roots()
    # spot checks: norms are 2, ip in {-1,0,1}
    for v in R[:10]:
        assert dot(v, v) == _Q(2)
    ips = {dot(R[0], R[i]) for i in range(1, 240)}
    assert ips.issubset({_Q(-2), _Q(-1), _Q(0), _Q(1)})


def test_no_float_in_dependency_tree():
    import subprocess
    import sys

    p = subprocess.run(
        [sys.executable, "util/no_float_lint.py"],
        capture_output=True,
        text=True,
    )
    assert p.returncode == 0, f"float usage detected:\n{p.stdout}\n{p.stderr}"
