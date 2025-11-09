from __future__ import annotations

from fractions import Fraction as Q

from atlas.atlas import make_atlas
from core.morphism import Morphism
from core.resgraph import ResGraph
from core.weyl import WeylAction


def v(*xs: int) -> tuple[Q, ...]:
    return tuple(Q(x) for x in xs)


def test_phi_edges_end_to_end() -> None:
    V = frozenset({"a", "b", "c"})
    labels = {
        "a": v(1, 0),
        "b": v(0, 1),
        "c": v(-1, 0),
    }
    U = frozenset({"a"})
    A = make_atlas(V, labels, U)

    assert A.is_adjacent("a", "c")
    assert not A.is_adjacent("a", "b")
    assert not A.is_adjacent("b", "c")
    assert A.E == frozenset({("a", "c")})


def test_morphism_identity_and_unity() -> None:
    V = frozenset({"a", "c"})
    labels = {"a": v(1, 0), "c": v(-1, 0)}
    U = frozenset({"a"})
    A = make_atlas(V, labels, U)
    Id = WeylAction(M=((Q(1), Q(0)), (Q(0), Q(1))))
    f = {"a": "a", "c": "c"}
    m = Morphism(src=A, dst=A, f=f, w=Id)
    m.check()


def test_morphism_with_reflection() -> None:
    V = frozenset({"a", "c"})
    labels = {"a": v(1, 0), "c": v(-1, 0)}
    U = frozenset({"a", "c"})
    A = make_atlas(V, labels, U)

    R = WeylAction(M=((Q(-1), Q(0)), (Q(0), Q(1))))
    f = {"a": "c", "c": "a"}
    m = Morphism(src=A, dst=A, f=f, w=R)
    m.check()
