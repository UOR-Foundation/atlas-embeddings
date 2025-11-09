from collections import Counter
from atlas12288.schedule import C768Schedule


def test_c768_bijective_over_full_cycle():
    sch = C768Schedule()
    seen = set(sch.iterate(12288))
    assert len(seen) == 12288


def test_c768_marginals_stationary_every_window():
    sch = C768Schedule()
    for start in (0, 193, 768, 1024, 4096):
        pages, bytes_ = sch.window_counts(start)
        assert all(v == 16 for v in pages.values())
        assert all(v == 3 for v in bytes_.values())
