from __future__ import annotations

from views.api import load_atlas_from_json, view_r96_from_iota
from views.exceptional import view_E6, view_E7, view_E8, view_F4, view_G2


def test_exceptional_views_roundtrip() -> None:
    atlas = load_atlas_from_json()
    for fn in [view_G2, view_F4, view_E6, view_E7, view_E8]:
        view = fn(atlas)
        assert view.meta["type"] in {"G2", "F4", "E6", "E7", "E8", "Unknown"}
        for u in view.graph.V:
            for v in view.graph.V:
                if u == v:
                    continue
                view.graph.is_adjacent(u, v)


def test_r96_view_is_cayley_free_and_plus1() -> None:
    iota = list(range(96))
    view = view_r96_from_iota(iota)
    assert view.meta["phi"] == "+1"
    assert view.meta["cayley_free"] is True
    assert view.graph.Φ(1) is True
    assert view.graph.Φ(-1) is False
