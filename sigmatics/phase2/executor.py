#!/usr/bin/env python3
"""
Phase 2 — Executor and Evaluator (Sigmatics × Multiplicity)

Implements:
- Executor: R^k, Π_{p^r}, Δ_{p^r}, A^{(p^r)}, minimal split/merge/fold.
  • Signal path (X ∈ ℝ^n): cyclic shift, permutations, residue-class projectors.
  • Relation path (H): adjacency dicts with quotient-contraction modulo m, relabel under permutations/rotations.
  • Logging: JSONL trace with per-op stats.

- Evaluator: resonance metrics vs trivial baselines.
  • EVR (energy explained ratio) after Π/A and Δ.
  • Residue-bucket retrieval uplift vs random-permutation baseline.
  • Relation consistency after split/merge (Jaccard on edge sets).

Artifacts:
- program.json   (resolved program with n and obligations carried through)
- trace.jsonl    (one JSON object per executed step)
- metrics.json   (summary metrics)

UNPROVEN policies: permPolicy, arityPolicy, markMode semantics for relation Δ/A. Emitted as obligations and noted in trace.
"""
from __future__ import annotations
import argparse, json, math, os, random, statistics, time
from dataclasses import dataclass, field
from typing import Any, Dict, List, Tuple, Iterable
import numpy as np

# -------------------------
# Constants and helpers
# -------------------------
N = 12288
PAGE_SIZE = 256
PAGES = N // PAGE_SIZE

np.set_printoptions(suppress=True, linewidth=120)

# ---------- Indexing ----------

def index_map(page: int, belt: int, offset: int, B: int | None = None) -> int:
    if page < 0 or page >= PAGES:
        raise ValueError("page out of range")
    if offset < 0 or offset >= PAGE_SIZE:
        raise ValueError("offset out of range")
    if B is None:
        return page*PAGE_SIZE + offset
    if belt < 0 or belt >= B:
        raise ValueError("belt out of range for B")
    if page >= (N // (PAGE_SIZE*B)):
        raise ValueError("page out of range for chosen B packing")
    return page*(PAGE_SIZE*B) + belt*PAGE_SIZE + offset

# ---------- Policies (UNPROVEN) ----------

class Policies:
    @staticmethod
    def primePolicy(d: Dict[str, Any]) -> int:
        return int(d.get("p", 3))
    @staticmethod
    def levelPolicy(d: Dict[str, Any]) -> int:
        return int(d.get("r", 1))
    @staticmethod
    def markMode(d: Dict[str, Any]) -> str:
        # "Δ" or "A". Default Δ unless explicitly "A" to surface residuals in v0 tests.
        return "A" if d.get("mode", "Δ") == "A" else "Δ"
    @staticmethod
    def permPolicy(ctx: Dict[str, Any], n: int) -> List[int]:
        # Identity until policy fixed.
        return list(range(n))
    @staticmethod
    def arityPolicy(ctx: Dict[str, Any]) -> int:
        return int(ctx.get("arity", 2))

def admissible(p: int, r: int, n: int = N) -> bool:
    return (n % (p**r)) == 0

# -------------------------
# Linear operators on X
# -------------------------

def rotate_Rk(x: np.ndarray, k: int) -> np.ndarray:
    k %= x.size
    if k == 0:
        return x.copy()
    return np.concatenate([x[-k:], x[:-k]])

def projector_A(x: np.ndarray, m: int) -> np.ndarray:
    """A^{(m)}: Project onto subspace constant on residue classes mod m."""
    n = x.size
    y = np.empty_like(x)
    for c in range(m):
        idx = np.arange(c, n, m)
        mean_val = float(np.mean(x[idx]))
        y[idx] = mean_val
    return y

def projector_Delta(x: np.ndarray, m: int) -> np.ndarray:
    """Δ_{(m)}: Orthogonal complement projector = (I - A^{(m)})."""
    return x - projector_A(x, m)

# -------------------------
# Graph H utilities
# -------------------------
# H represented as adjacency dict: {u: sorted(list(neigh))}

def make_ring_graph(n: int) -> Dict[int, List[int]]:
    H = {i: [ (i+1) % n ] for i in range(n)}
    return H

def edges_of(H: Dict[int, List[int]]) -> List[Tuple[int,int]]:
    E = []
    for u, vs in H.items():
        for v in vs:
            E.append((u, v))
    return E

def from_edges(n: int, E: Iterable[Tuple[int,int]]) -> Dict[int, List[int]]:
    H: Dict[int, List[int]] = {i: [] for i in range(n)}
    for u, v in E:
        H[u].append(v)
    for u in H:
        H[u] = sorted(set(H[u]))
    return H

def permute_nodes(H: Dict[int, List[int]], pi: List[int]) -> Dict[int, List[int]]:
    # Map node i -> pi[i]
    n = len(H)
    mapping = {i: pi[i] for i in range(n)}
    E2 = [ (mapping[u], mapping[v]) for (u,v) in edges_of(H) ]
    return from_edges(n, E2)

def rotate_graph(H: Dict[int, List[int]], k: int) -> Dict[int, List[int]]:
    n = len(H)
    k %= n
    if k == 0:
        return {u: vs[:] for u,vs in H.items()}
    f = lambda u: (u + k) % n
    return from_edges(n, [ (f(u), f(v)) for (u,v) in edges_of(H) ])

def quotient_graph_mod(H: Dict[int, List[int]], m: int) -> Dict[int, List[int]]:
    # Contract nodes by residue modulo m; nodes become 0..m-1
    E = set()
    for (u, v) in edges_of(H):
        E.add((u % m, v % m))
    Hq: Dict[int, List[int]] = {c: [] for c in range(m)}
    for (a, b) in sorted(E):
        Hq[a].append(b)
    for c in Hq:
        Hq[c] = sorted(set(Hq[c]))
    return Hq

def jaccard_edges(E1: Iterable[Tuple[int,int]], E2: Iterable[Tuple[int,int]]) -> float:
    S1, S2 = set(E1), set(E2)
    if not S1 and not S2:
        return 1.0
    return len(S1 & S2) / float(len(S1 | S2))

# -------------------------
# Trace logger
# -------------------------

class Trace:
    def __init__(self, path: str):
        self.path = path
        self.fh = open(path, "w", encoding="utf-8")
    def log(self, rec: Dict[str, Any]):
        self.fh.write(json.dumps(rec, ensure_ascii=False) + "\n")
    def close(self):
        self.fh.close()

# -------------------------
# Executor
# -------------------------

@dataclass
class ExecState:
    x: np.ndarray
    H: Dict[int, List[int]]
    context: Dict[str, Any] = field(default_factory=dict)

class Executor:
    def __init__(self, policies: Policies, trace: Trace):
        self.policies = policies
        self.trace = trace

    def step(self, w: Dict[str, Any], st: ExecState):
        op = w["op"]
        t0 = time.time()
        rec: Dict[str, Any] = {"op": op, "note": w.get("note")}
        n = st.x.size

        def stats(x: np.ndarray) -> Dict[str, Any]:
            sse = float(np.dot(x, x))
            return {"energy": sse, "mean": float(np.mean(x)), "std": float(np.std(x))}

        rec["pre"] = stats(st.x)
        if op == "copy":
            y = st.x
        elif op == "rotate":
            y = rotate_Rk(st.x, int(w.get("k", 0)))
            st.H = rotate_graph(st.H, int(w.get("k", 0)))
        elif op == "permute":
            pi = w.get("pi")
            if pi is None or len(pi) != n:
                pi = self.policies.permPolicy({"op":"permute"}, n)
                rec["policy"] = "permPolicy:UNPROVEN"
            y = st.x[np.array(pi)]
            st.H = permute_nodes(st.H, pi)
        elif op == "projector":
            p, r = int(w["p"]), int(w["r"])
            if not admissible(p, r, n):
                raise ValueError(f"Admissibility failed: p^{r} !| {n}")
            m = p**r
            mode = w.get("mode", self.policies.markMode({}))
            st.context["last_m"] = m
            st.context["last_mark_mode"] = mode
            if mode == "A":
                y = projector_A(st.x, m)
                # relation path: quotient
                st.H = quotient_graph_mod(st.H, m)
            else:  # Δ
                y = projector_Delta(st.x, m)
                # relation path: keep H unchanged but record residual multiplicity
                pass
            rec["mark"] = {"p": p, "r": r, "m": m, "mode": mode}
        elif op == "split":
            # Minimal: record split granularity m. If available from context, reuse.
            m = st.context.get("last_m", 3)
            st.context["split_m"] = m
            st.context["split_ellType"] = w.get("ellType")
            # relation: replace H with quotient to inspect structure per class
            st.H = quotient_graph_mod(st.H, m)
            y = st.x
        elif op == "merge":
            # Minimal: no true inverse lift; just keep current H and note arity.
            st.context.pop("split_m", None)
            st.context.pop("split_ellType", None)
            y = st.x
        elif op == "modal_enter" or op == "modal_exit":
            # Structured no-ops with logging.
            y = st.x
            rec["modal"] = op
        else:
            raise ValueError(f"Unknown op: {op}")

        st.x = y
        rec["post"] = stats(st.x)
        rec["dt_ms"] = int(1000*(time.time()-t0))
        self.trace.log(rec)
        return st

# -------------------------
# Evaluator
# -------------------------

def energy_ratio(x: np.ndarray, y: np.ndarray) -> float:
    num = float(np.dot(y, y))
    den = float(np.dot(x, x)) if float(np.dot(x, x)) != 0.0 else 1.0
    return num / den

def random_baseline_evr(x: np.ndarray, m: int, trials: int = 50, seed: int = 7) -> Tuple[float, float]:
    rng = random.Random(seed)
    n = x.size
    evrs: List[float] = []
    for _ in range(trials):
        pi = list(range(n))
        rng.shuffle(pi)
        xp = x[np.array(pi)]
        yp = projector_A(xp, m)
        evrs.append(energy_ratio(xp, yp))
    return float(statistics.mean(evrs)), float(statistics.pstdev(evrs))

def retrieval_uplift(x: np.ndarray, m: int, trials: int = 50, seed: int = 11) -> Dict[str, float]:
    # Predictor: class mean per residue. Score R^2 vs random-permutation baseline.
    n = x.size
    yhat = projector_A(x, m)
    ss_tot = float(np.var(x) * n)
    ss_res = float(np.dot(x - yhat, x - yhat))
    r2 = 1.0 - (ss_res / ss_tot if ss_tot > 0 else 1.0)
    # Baseline
    rng = random.Random(seed)
    r2s = []
    for _ in range(trials):
        pi = list(range(n)); rng.shuffle(pi)
        xp = x[np.array(pi)]
        yhatp = projector_A(xp, m)
        ss_tot_p = float(np.var(xp) * n)
        ss_res_p = float(np.dot(xp - yhatp, xp - yhatp))
        r2s.append(1.0 - (ss_res_p / ss_tot_p if ss_tot_p > 0 else 1.0))
    return {"r2": r2, "baseline_mean": float(statistics.mean(r2s)), "baseline_std": float(statistics.pstdev(r2s))}

def relation_consistency(original_H: Dict[int, List[int]], split_H: Dict[int, List[int]], merged_H: Dict[int, List[int]]) -> Dict[str, float]:
    # Compare edge sets at each stage
    E0 = edges_of(original_H)
    Es = edges_of(split_H)
    Em = edges_of(merged_H)
    return {
        "jaccard_orig_split": jaccard_edges(E0, Es),
        "jaccard_split_merge": jaccard_edges(Es, Em),
        "jaccard_orig_merge": jaccard_edges(E0, Em),
        "|E0|": float(len(E0)), "|Es|": float(len(Es)), "|Em|": float(len(Em))
    }

# -------------------------
# Runner
# -------------------------

def run(program: Dict[str, Any], outdir: str, seed: int = 42) -> Dict[str, Any]:
    os.makedirs(outdir, exist_ok=True)
    # Save resolved program copy
    with open(os.path.join(outdir, "program.json"), "w", encoding="utf-8") as f:
        json.dump(program, f, indent=2, ensure_ascii=False)

    rng = np.random.default_rng(seed)
    x0 = rng.normal(size=N)
    H0 = make_ring_graph(N)

    trace = Trace(os.path.join(outdir, "trace.jsonl"))
    execu = Executor(Policies(), trace)

    st = ExecState(x=x0.copy(), H={u: vs[:] for u, vs in H0.items()}, context={})

    # Execute
    for w in program.get("words", []):
        st = execu.step(w, st)
    trace.close()

    # Metrics
    m = st.context.get("last_m", 3)
    Ax = projector_A(x0, m)
    Dx = projector_Delta(x0, m)
    metrics: Dict[str, Any] = {
        "n": N,
        "last_m": m,
        "evr_A": energy_ratio(x0, Ax),
        "evr_Delta": energy_ratio(x0, Dx),
        "baseline_evr_A": {
            "mean": None,
            "std": None
        },
        "retrieval_uplift": retrieval_uplift(x0, m)
    }
    mu, su = random_baseline_evr(x0, m, trials=50, seed=seed+1)
    metrics["baseline_evr_A"]["mean"] = mu
    metrics["baseline_evr_A"]["std"] = su

    # Relation consistency using a synthetic split/merge pass if present
    split_H = quotient_graph_mod(H0, m)
    merged_H = split_H  # minimal v0: treat merge as identity on quotient
    metrics["relation_consistency"] = relation_consistency(H0, split_H, merged_H)

    with open(os.path.join(outdir, "metrics.json"), "w", encoding="utf-8") as f:
        json.dump(metrics, f, indent=2, ensure_ascii=False)

    return metrics

# -------------------------
# CLI
# -------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--program", required=True, help="compiled_program.json from Phase 1")
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--seed", type=int, default=42)
    args = ap.parse_args()

    with open(args.program, "r", encoding="utf-8") as f:
        program = json.load(f)
    metrics = run(program, args.outdir, seed=args.seed)
    print(json.dumps({"outdir": args.outdir, "summary": metrics}, indent=2))

if __name__ == "__main__":
    main()
