from __future__ import annotations
from dataclasses import dataclass
from typing import Dict, List, Tuple, Iterable, Set

# ---------------------------
# Prime signatures per axis
# ---------------------------


def _factor_int(n: int) -> Dict[int, int]:
    """Prime factorization as {prime: exponent}. n>=1. No floats."""
    if n < 1:
        raise ValueError("n must be >=1")
    out: Dict[int, int] = {}
    x = n
    p = 2
    while p * p <= x:
        while x % p == 0:
            out[p] = out.get(p, 0) + 1
            x //= p
        p = 3 if p == 2 else p + 2  # 2,3,5,7,...
    if x > 1:
        out[x] = out.get(x, 0) + 1
    return out


def axis_signature(length: int) -> Dict[int, int]:
    """σ for a single axis length n = ∏ p^{e_p}."""
    return _factor_int(length)


def tensor_signature(axis_lengths: Iterable[int]) -> Dict[int, int]:
    """Combine axis signatures by addition of exponents."""
    sig: Dict[int, int] = {}
    for n in axis_lengths:
        for p, e in axis_signature(int(n)).items():
            sig[p] = sig.get(p, 0) + e
    return sig


def add_signatures(sigA: Dict[int, int], sigB: Dict[int, int]) -> Dict[int, int]:
    out: Dict[int, int] = dict(sigA)
    for p, e in sigB.items():
        out[p] = out.get(p, 0) + e
    return out


def eq_signatures(sigA: Dict[int, int], sigB: Dict[int, int]) -> bool:
    # normalize zeros
    keys = set(sigA.keys()) | set(sigB.keys())
    for k in keys:
        if sigA.get(k, 0) != sigB.get(k, 0):
            return False
    return True


# ---------------------------
# Certificates
# ---------------------------


def cert_tensor_product(sigA: Dict[int, int], sigB: Dict[int, int], sigOut: Dict[int, int]) -> bool:
    """C_⊗ : signatures add under ⊗."""
    return eq_signatures(add_signatures(sigA, sigB), sigOut)


def cert_contraction(
    axesA: List[int],
    axesB: List[int],
    pairings: List[Tuple[int, int]],
) -> bool:
    """
    C_{<·,·>}: matched axes cancel.
    axesA: lengths of A's axes
    axesB: lengths of B's axes
    pairings: list of (i,j) to contract A_i with B_j
    Requires: for each (i,j), signature(axis_i) == signature(axis_j).
    """
    for i, j in pairings:
        if not eq_signatures(axis_signature(axesA[i]), axis_signature(axesB[j])):
            return False
    return True


# ---------------------------
# Ledger for channels
# ---------------------------


@dataclass
class ChannelRow:
    id: str
    sigma: Dict[int, int]          # prime -> exponent
    budget: int                    # integer budget units
    commutator_class: str


class PETCLedger:
    def __init__(self) -> None:
        self.rows: Dict[str, ChannelRow] = {}
        self.commutator_budget: Dict[str, int] = {}  # class -> remaining units

    def add_channel(self, row: ChannelRow) -> None:
        if row.id in self.rows:
            raise ValueError("duplicate channel id")
        self.rows[row.id] = row
        if row.commutator_class not in self.commutator_budget:
            self.commutator_budget[row.commutator_class] = row.budget

    def decrement_commutator(self, comm_class: str, amount: int = 1) -> int:
        if amount < 0:
            raise ValueError("amount must be >=0")
        if comm_class not in self.commutator_budget:
            raise KeyError("unknown commutator class")
        rem = self.commutator_budget[comm_class]
        if rem < amount:
            raise RuntimeError("commutator budget breach")
        rem -= amount
        self.commutator_budget[comm_class] = rem
        return rem

    def get_budget(self, comm_class: str) -> int:
        return self.commutator_budget.get(comm_class, 0)


# ---------------------------
# Group gate: U ≅ (Z/2)^11 on G = P × B
# ---------------------------
# |P| = 48, |B| = 256, so |G| = 48*256 = 12288.
# Partition G into six orbits indexed by r in {0..5}.
# Map (p,b) -> (r, idx) where:
#   r   = p // 8  ∈ {0..5}
#   idx = (p % 8)*256 + b  ∈ {0..2047}
# Action of U (size 2^11 = 2048) on each orbit:
#   for u ∈ {0..2047}, act_u(r, idx) = (r, (idx + u) mod 2048)
# This action is free and transitive on each orbit.


def pack_rb(p: int, b: int) -> Tuple[int, int]:
    if not (0 <= p < 48 and 0 <= b < 256):
        raise ValueError("p in [0,47], b in [0,255]")
    r = p // 8
    idx = (p % 8) * 256 + b
    return r, idx


def unpack_rb(r: int, idx: int) -> Tuple[int, int]:
    if not (0 <= r < 6 and 0 <= idx < 2048):
        raise ValueError("r in [0,5], idx in [0,2047]")
    p = 8 * r + (idx // 256)
    b = idx % 256
    return p, b


def act_U(p: int, b: int, u: int) -> Tuple[int, int]:
    r, idx = pack_rb(p, b)
    u_mod = u & 2047  # modulo 2048
    idx2 = (idx + u_mod) & 2047
    return unpack_rb(r, idx2)


# Anchors S = {(8m, 0)} for m=0..5

def anchors_S() -> List[Tuple[int, int]]:
    return [(8*m, 0) for m in range(6)]


# Phi schedule: order-768 permutation
# Phi(p,b) = ( (p+16) mod 48, (b+1) mod 256 ).
# Order(16 mod 48) = 3. Order(1 mod 256) = 256. lcm(3,256)=768.

def Phi(p: int, b: int) -> Tuple[int, int]:
    return ((p + 16) % 48, (b + 1) % 256)


def phi_pow(p: int, b: int, k: int) -> Tuple[int, int]:
    # repeated application without floats
    p2 = (p + (16 * (k % 48))) % 48
    b2 = (b + (k % 256)) % 256
    return (p2, b2)


# Verifications for CI


def verify_freeness_sample(samples: int = 32) -> bool:
    """Sampled freeness check: for nonzero u, act_u(g) != g."""
    gs = anchors_S()
    # extend with a few neighbors per orbit
    for r in range(6):
        for j in (1, 255, 511, 1023, 2047):
            gs.append(unpack_rb(r, j))
    us = [1, 2, 3, 7, 11, 17, 255, 1023, 2047]
    cnt = 0
    for (p, b) in gs:
        for u in us:
            cnt += 1
            if act_U(p, b, u) == (p, b):
                return False
            if cnt >= samples:
                return True
    return True


def verify_orbit_counts() -> bool:
    """Exactly six disjoint orbits, each of size 2048."""
    seen: Set[Tuple[int, int]] = set()
    for r in range(6):
        # orbit from anchor (8*r,0)
        start = (8*r, 0)
        orb: Set[Tuple[int, int]] = set()
        for u in range(2048):
            orb.add(act_U(start[0], start[1], u))
        if len(orb) != 2048:
            return False
        # disjointness
        if any(g in seen for g in orb):
            return False
        seen |= orb
    return len(seen) == 48 * 256


def verify_C768_closure() -> bool:
    """Phi^768 = id on all anchors (suffices)."""
    for p, b in anchors_S():
        if phi_pow(p, b, 768) != (p, b):
            return False
    return True


def verify_phi_equivariance_sample(samples: int = 64, debug: bool = False) -> bool:
    from petc.phi import verify_phi_equivariance_sample as _verify_phi_equivariance_sample

    gs = anchors_S()
    for r in range(6):
        for j in (5, 73, 511, 777, 1311):
            gs.append(unpack_rb(r, j & 2047))

    def int_to_bits(u: int) -> tuple[int, ...]:
        return tuple((u >> k) & 1 for k in range(11))

    us = [int_to_bits(u) for u in [0, 1, 2, 3, 7, 15, 31, 63, 127, 255, 511, 1023, 2047]]

    def phi_pair(g: tuple[int, int]) -> tuple[int, int]:
        return Phi(g[0], g[1])

    def act_u_on_g(u_bits: tuple[int, ...], g: tuple[int, int]) -> tuple[int, int]:
        u_int = 0
        for idx, bit in enumerate(u_bits):
            if bit:
                u_int |= 1 << idx
        return act_U(g[0], g[1], u_int)

    return _verify_phi_equivariance_sample(
        gs,
        us,
        phi_pair,
        act_u_on_g,
        act_u_on_g,
        max_checks=samples,
        debug=debug,
    )
