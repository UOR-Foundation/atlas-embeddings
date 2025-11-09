from __future__ import annotations
from typing import Iterable, Tuple


def verify_phi_equivariance_sample(
    G_elems: Iterable[Tuple[int, int]],
    U_actions: Iterable[Tuple[int, ...]],
    Phi,
    act_U_on_G,
    act_U_on_Y,
    max_checks: int = 1024,
    debug: bool = False,
) -> bool:
    cnt = 0
    for g in G_elems:
        y = Phi(g)
        for u in U_actions:
            lhs = act_U_on_Y(u, y)
            rhs = Phi(act_U_on_G(u, g))
            ok = lhs == rhs
            if not ok and debug:
                print(
                    "Φ-equivariance fail",
                    {"u": u, "g": g, "Phi(g)": y, "u·Phi(g)": lhs, "Phi(u·g)": rhs},
                )
                return False
            cnt += 1
            if cnt >= max_checks:
                return True
    return True
