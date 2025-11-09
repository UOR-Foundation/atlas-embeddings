from __future__ import annotations

from fractions import Fraction as Q

from atlas.atlas import make_atlas
from atlas.embedding import embed_atlas_to_e8
from core.resgraph import ResGraph
from e8.roots import dot, generate_e8_roots


def make_synthetic_atlas_from_e8_subset() -> ResGraph:
    roots = generate_e8_roots()
    idxs = list(range(96))
    V = frozenset(f"v{i}" for i in range(96))
    labels = {f"v{i}": roots[idxs[i]] for i in range(96)}
    U = frozenset({"v0"})
    return make_atlas(V, labels, U)


def test_embedding_produces_96_and_certifies_pairs() -> None:
    atlas = make_synthetic_atlas_from_e8_subset()
    res = embed_atlas_to_e8(atlas)
    assert len(res.f) == 96
    verts = sorted(atlas.V)
    for i, u in enumerate(verts):
        for j in range(i + 1, len(verts)):
            v = verts[j]
            ip = dot(res.roots[res.f[u]], res.roots[res.f[v]])
            assert (ip == Q(-1)) == atlas.is_adjacent(u, v)
    assert len(res.log.splitlines()) == 1 + 4560
