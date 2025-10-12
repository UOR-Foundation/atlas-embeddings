from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction as Q
from hashlib import sha256
from typing import Dict, Iterable, List, Optional

from atlas.uniqueness import matrix_between_embeddings, permutes_root_set
from core.resgraph import ResGraph, Vertex
from e8.roots import Vector, dot, generate_e8_roots

RootIndex = int


@dataclass(frozen=True)
class EmbeddingResult:
    f: Dict[Vertex, RootIndex]
    roots: List[Vector]
    matrix_cert: Optional[List[List[Q]]]
    checksum_coords: str
    log: str


def _vertex_order(V: Iterable[Vertex]) -> List[Vertex]:
    return sorted(V)


def _direct_embedding(G: ResGraph, R: List[Vector]) -> Optional[Dict[Vertex, int]]:
    vector_index = {v: i for i, v in enumerate(R)}
    f: Dict[Vertex, int] = {}
    used: set[int] = set()
    for u in _vertex_order(G.V):
        label = G.λ[u]
        idx = vector_index.get(label)
        if idx is None or idx in used:
            return None
        f[u] = idx
        used.add(idx)
    return f


def _candidate_roots_for_vertex(
    u: Vertex,
    R: List[Vector],
    G: ResGraph,
    vector_index: Dict[Vector, int],
    length_index: Dict[Q, List[int]],
) -> List[int]:
    label = G.λ[u]
    if label in vector_index:
        return [vector_index[label]]
    length = sum(x * x for x in label)
    candidates = length_index.get(length)
    if candidates is None:
        return list(range(len(R)))
    return list(candidates)


def _independent(span: List[Vector], v: Vector) -> bool:
    if not span:
        return True
    m = len(span)
    A = [[span[j][i] for j in range(m)] for i in range(8)]
    b = [v[i] for i in range(8)]

    def rank(M: List[List[Q]]) -> int:
        if not M:
            return 0
        M = [row[:] for row in M]
        n = len(M)
        p = len(M[0])
        r = 0
        c = 0
        while r < n and c < p:
            pivot = None
            for i in range(r, n):
                if M[i][c] != 0:
                    pivot = i
                    break
            if pivot is None:
                c += 1
                continue
            M[r], M[pivot] = M[pivot], M[r]
            piv = M[r][c]
            for j in range(c, p):
                M[r][j] /= piv
            for i in range(n):
                if i == r:
                    continue
                factor = M[i][c]
                if factor == 0:
                    continue
                for j in range(c, p):
                    M[i][j] -= factor * M[r][j]
            r += 1
            c += 1
        return r

    r1 = rank([row[:] for row in A])
    A2 = [A[i] + [b[i]] for i in range(8)]
    r2 = rank(A2)
    return r2 > r1


def _choose_basis_vertices(order: List[Vertex], f: Dict[Vertex, int], R: List[Vector]) -> List[Vertex]:
    span: List[Vector] = []
    basis_vertices: List[Vertex] = []
    for u in order:
        v = R[f[u]]
        if _independent(span, v):
            basis_vertices.append(u)
            span.append(v)
        if len(basis_vertices) == 8:
            break
    if len(basis_vertices) != 8:
        raise ValueError("could not find rank-8 subset")
    return basis_vertices


def _search_embedding(
    G: ResGraph, R: List[Vector], order_override: Optional[List[Vertex]] = None
) -> Dict[Vertex, int]:
    order = order_override or _vertex_order(G.V)
    neighbor_map: Dict[Vertex, List[Vertex]] = {
        u: sorted(G.neighbors(u)) for u in order
    }
    deg = {u: len(neighbor_map[u]) for u in order}
    vars_ = sorted(order, key=lambda u: (-deg[u], u))
    vector_index = {v: i for i, v in enumerate(R)}
    length_index: Dict[Q, List[int]] = {}
    for i, v in enumerate(R):
        l = dot(v, v)
        length_index.setdefault(l, []).append(i)
    domains: Dict[Vertex, List[int]] = {
        u: _candidate_roots_for_vertex(u, R, G, vector_index, length_index)
        for u in vars_
    }

    assign: Dict[Vertex, int] = {}
    used: set[int] = set()

    def consistent(u: Vertex, r_idx: int) -> bool:
        ru = R[r_idx]
        if dot(ru, ru) != Q(2):
            return False
        for v in neighbor_map[u]:
            if v in assign:
                rv = R[assign[v]]
                if (dot(ru, rv) == Q(-1)) != G.is_adjacent(u, v):
                    return False
        return True

    def backtrack(i: int) -> bool:
        if i == len(vars_):
            return True
        u = vars_[i]
        for r_idx in domains[u]:
            if r_idx in used:
                continue
            if not consistent(u, r_idx):
                continue
            assign[u] = r_idx
            used.add(r_idx)
            if backtrack(i + 1):
                return True
            used.remove(r_idx)
            del assign[u]
        return False

    if not backtrack(0):
        raise ValueError("no embedding found")
    return assign


def _pair_log(G: ResGraph, f: Dict[Vertex, int], R: List[Vector]) -> str:
    verts = _vertex_order(G.V)
    lines: List[str] = []
    violations = 0
    for i, u in enumerate(verts):
        for j in range(i + 1, len(verts)):
            v = verts[j]
            adj = G.is_adjacent(u, v)
            ip = dot(R[f[u]], R[f[v]])
            ok = (ip == Q(-1)) == adj
            if not ok:
                violations += 1
            lines.append(f"{u},{v}: adj={int(adj)} ip={ip}")
    digest = sha256(("\n".join(lines)).encode()).hexdigest()
    header = f"pairs=4560 violations={violations} sha256={digest}"
    return "\n".join([header] + lines)


def _matrix_certificate(
    G: ResGraph,
    R: List[Vector],
    f1: Dict[Vertex, int],
    f_alt: Optional[Dict[Vertex, int]] = None,
) -> Optional[List[List[Q]]]:
    order = _vertex_order(G.V)
    if f_alt is None:
        try:
            f_alt = _search_embedding(G, R, list(reversed(order)))
        except ValueError:
            return None
    basis_vertices = _choose_basis_vertices(order, f1, R)
    S1 = [R[f1[u]] for u in basis_vertices]
    S2 = [R[f_alt[u]] for u in basis_vertices]
    M = matrix_between_embeddings(S1, S2)
    if permutes_root_set(M, R):
        return M
    return None


def embed_atlas_to_e8(G: ResGraph) -> EmbeddingResult:
    R = generate_e8_roots()
    f_direct = _direct_embedding(G, R)
    if f_direct is not None:
        f = f_direct
        matrix_cert = _matrix_certificate(G, R, f, f)
    else:
        f = _search_embedding(G, R)
        matrix_cert = _matrix_certificate(G, R, f)
    if len(set(f.values())) != len(G.V):
        raise ValueError("embedding is not injective")
    log = _pair_log(G, f, R)
    coords = [R[f[u]] for u in _vertex_order(G.V)]
    flat = [str(x) for row in coords for x in row]
    checksum_coords = sha256((",".join(flat)).encode()).hexdigest()
    return EmbeddingResult(
        f=f,
        roots=R,
        matrix_cert=matrix_cert,
        checksum_coords=checksum_coords,
        log=log,
    )
