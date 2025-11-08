from atlas12288.anchors import ANCHORS
from atlas12288.complex import BoundaryComplex


def test_orbit_sizes_and_uniqueness():
    C = BoundaryComplex()
    seen = set()
    # Each anchor gives 2^11 cells
    for a, (pa, ba) in enumerate(ANCHORS):
        orbit = [C.cell_from(a, g) for g in range(2048)]
        assert len(orbit) == 2048
        assert len(set(orbit)) == 2048
        seen.update(orbit)
    # Total is 12,288
    assert len(seen) == 12288


def test_neighbors_degree():
    C = BoundaryComplex()
    neigh = list(C.neighbors(0, 0))
    assert len(neigh) == 11
