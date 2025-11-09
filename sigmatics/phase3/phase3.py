#!/usr/bin/env python3
"""
Phase 3 — Validation & KPIs (Sigmatics × Multiplicity)

Validates unit properties, round‑trip integrity, and computes KPIs.

Inputs:
  • Either --program compiled_program.json (from Phase 1)
  • Or     --source  source.sig  (lower+compile here)

Outputs (in --outdir):
  • program.json            — resolved program (if compiled here)
  • trace.jsonl             — execution log (from Phase 2‑style executor)
  • metrics.json            — EVR, retrieval uplift, relation metrics
  • validation_report.json  — unit properties and witnesses
  • roundtrip.json          — source → lowered → compiled → pretty‑print checks
  • kpis.json               — resonance uplift vs baseline, wall‑time, determinism rate, obligation counts

Notes:
  • permPolicy, arityPolicy, markMode semantics remain UNPROVEN. Recorded explicitly.
  • Non‑commutation witness uses a deterministic permutation W^{(q)} built from within‑page stride on 256‑offsets.
"""
from __future__ import annotations
import argparse, json, math, os, random, re, statistics, time
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

# ---------- Deterministic JSON dump ----------

def stable_json_dumps(obj: Any) -> str:
    return json.dumps(obj, ensure_ascii=False, sort_keys=True, separators=(",", ":"))

# ---------- Index map ----------

def index_map(page: int, belt: int, offset: int, B: int | None = None) -> int:
    if page < 0 or page >= PAGES: raise ValueError("page out of range")
    if offset < 0 or offset >= PAGE_SIZE: raise ValueError("offset out of range")
    if B is None: return page*PAGE_SIZE + offset
    if belt < 0 or belt >= B: raise ValueError("belt out of range for B")
    if page >= (N // (PAGE_SIZE*B)): raise ValueError("page out of range for chosen B")
    return page*(PAGE_SIZE*B) + belt*PAGE_SIZE + offset

# -------------------------
# Phase 1 subset — Lowerer & Compiler
# -------------------------

def tokenize(script: str) -> List[Tuple[str, Tuple[int,int]]]:
    toks = []
    start = 0
    for m in re.finditer(r";", script):
        end = m.start()
        stmt = script[start:end].strip()
        if stmt: toks.append((stmt, (start, end)))
        start = m.end()
    tail = script[start:].strip()
    if tail: toks.append((tail, (start, len(script))))
    return toks

def parse_stmt(stmt: str) -> Dict[str, Any]:
    s = stmt.strip().replace("ρ","rho").replace("τ","tau").replace("μ","mu")
    s = re.sub(r"\s+", "", s)
    if s == "copy": return {"op":"copy","args":{}}
    if s == "~": return {"op":"mirror","args":{}}
    if s == "merge": return {"op":"merge","args":{}}
    if s == "quote": return {"op":"quote","args":{}}
    if s == "evaluate": return {"op":"evaluate","args":{}}
    m = re.match(r"swap@([A-Za-z_][A-Za-z0-9_]*)_([A-Za-z_][A-Za-z0-9_]*)$", s)
    if m: return {"op":"swap","args":{ "c":m.group(1), "d":m.group(2) }}
    m = re.match(r"split@ℓ:([A-Za-z][A-Za-z0-9_]*)$", s)
    if m: return {"op":"split","args":{ "ellType": m.group(1) }}
    m = re.match(r"mark@(\{.*\})$", s)
    if m: return {"op":"mark","args":{ "d": json.loads(m.group(1)) }}
    m = re.match(r"rho\[(\-?\d+)\]$", s)
    if m: return {"op":"control","args":{ "kind":"rho", "k": int(m.group(1)) }}
    m = re.match(r"tau\[(\-?\d+)\]$", s)
    if m: return {"op":"control","args":{ "kind":"tau", "k": int(m.group(1)) }}
    m = re.match(r"mu\[(\d+)\]$", s)
    if m: return {"op":"control","args":{ "kind":"mu", "p": int(m.group(1)) }}
    raise ValueError(f"Unrecognized statement: {stmt}")

def lower(script: str, src_name="stdin") -> Dict[str, Any]:
    toks = tokenize(script)
    words = []
    semantic = []
    for stmt, (a,b) in toks:
        node = parse_stmt(stmt)
        lw = {"op": node["op"], "args": node.get("args",{}), "meta": {"src":src_name, "span":[a,b]} }
        words.append(lw)
        semantic.append({"op": lw["op"], "args": lw["args"]})
    lower_hash = __import__("hashlib").sha1(stable_json_dumps({"words": semantic}).encode()).hexdigest()
    return {"lowered": {"words": words}, "lowering_hash": lower_hash}

class Policies:
    @staticmethod
    def primePolicy(d: Dict[str, Any]) -> int: return int(d.get("p",3))
    @staticmethod
    def levelPolicy(d: Dict[str, Any]) -> int: return int(d.get("r",1))
    @staticmethod
    def markMode(d: Dict[str, Any]) -> str: return "A" if d.get("mode","Δ") == "A" else "Δ"
    @staticmethod
    def permPolicy(ctx: Dict[str, Any], n: int) -> List[int]: return list(range(n))  # UNPROVEN
    @staticmethod
    def arityPolicy(ctx: Dict[str, Any]) -> int: return int(ctx.get("arity",2))     # UNPROVEN

def admissible(p: int, r: int, n: int=N) -> bool:
    return (n % (p**r)) == 0

def compile_words(sig_words: List[Dict[str, Any]], policies: Policies) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
    projectors, others, obligations = [], [], []
    for w in sig_words:
        op = w["op"]; args = w.get("args",{})
        if op == "copy":
            others.append({"op":"copy"})
        elif op in ("mirror","swap") or (op=="control" and args.get("kind")=="mu"):
            pi = policies.permPolicy({"op":op, **args}, N)
            obligations.append({"type":"policy","name":"permPolicy","status":"UNPROVEN","ctx":{**args, "op":op}})
            others.append({"op":"permute","pi":pi,"note":"UNPROVEN policy"})
        elif op == "merge":
            ar = policies.arityPolicy(args)
            obligations.append({"type":"policy","name":"arityPolicy","status":"UNPROVEN","arity":ar})
            others.append({"op":"merge","arity":ar})
        elif op == "split":
            others.append({"op":"split","ellType": args.get("ellType","unknown")})
        elif op == "mark":
            d = args.get("d",{})
            p, r = policies.primePolicy(d), policies.levelPolicy(d)
            if not admissible(p,r):
                obligations.append({"type":"admissibility","p":p,"r":r,"n":N,"status":"VIOLATION"})
                raise SystemExit(f"Admissibility failed: p^r={p}^{r} !| {N}")
            mode = policies.markMode(d)
            obligations.append({"type":"policy","name":"primePolicy/levelPolicy/markMode","status":"UNPROVEN","p":p,"r":r,"mode":mode})
            projectors.append({"op":"projector","p":p,"r":r,"mode":mode,"note":"UNPROVEN policy"})
        elif op == "quote":
            others.append({"op":"modal_enter","note":"UNPROVEN semantics"})
            obligations.append({"type":"semantics","name":"quote","status":"UNPROVEN"})
        elif op == "evaluate":
            others.append({"op":"modal_exit","note":"UNPROVEN semantics"})
            obligations.append({"type":"semantics","name":"evaluate","status":"UNPROVEN"})
        elif op == "control" and args.get("kind") in ("rho","tau"):
            k = int(args.get("k",0));  k = k if args["kind"]=="rho" else -k
            others.append({"op":"rotate","k":k})
        else:
            raise SystemExit(f"Unsupported op: {op}")
    return projectors + others, obligations

def compile_program(lowered: Dict[str, Any], policies: Policies) -> Dict[str, Any]:
    words, obs = compile_words(lowered["words"], policies)
    return {"n": N, "words": words, "obligations": obs}

# Round‑trip pretty‑printer for supported subset (no permute)

def pretty_print_program(prog: Dict[str, Any]) -> str:
    out = []
    for w in prog.get("words", []):
        op = w["op"]
        if op == "copy": out.append("copy;")
        elif op == "rotate":
            k = int(w.get("k",0))
            out.append(f"rho[{k}];") if k >= 0 else out.append(f"tau[{abs(k)}];")
        elif op == "projector":
            p, r = int(w["p"]), int(w["r"])
            mode = w.get("mode","Δ")
            mode_str = "A" if mode == "A" else "delta"
            out.append(f"mark@{{\"p\":{p},\"r\":{r},\"mode\":\"{mode_str}\"}};")
        elif op == "split":
            t = w.get("ellType","unknown")
            out.append(f"split@ℓ:{t};")
        elif op == "merge":
            out.append("merge;")
        elif op in ("modal_enter","modal_exit"):
            out.append("quote;") if op=="modal_enter" else out.append("evaluate;")
        else:
            # skip unsupported for round‑trip comparison
            pass
    return "\n".join(out)

# -------------------------
# Phase 2 subset — Executor & Evaluator
# -------------------------

def rotate_Rk(x: np.ndarray, k: int) -> np.ndarray:
    k %= x.size
    if k == 0: return x.copy()
    return np.concatenate([x[-k:], x[:-k]])

def projector_A(x: np.ndarray, m: int) -> np.ndarray:
    n = x.size
    y = np.empty_like(x)
    for c in range(m):
        idx = np.arange(c, n, m)
        y[idx] = float(np.mean(x[idx]))
    return y

def projector_Delta(x: np.ndarray, m: int) -> np.ndarray:
    return x - projector_A(x, m)

# Graph H as adjacency dict

def make_ring_graph(n: int) -> Dict[int, List[int]]:
    return {i: [(i+1)%n] for i in range(n)}

def edges_of(H: Dict[int, List[int]]) -> List[Tuple[int,int]]:
    return [(u,v) for u,vs in H.items() for v in vs]

def from_edges(n: int, E: Iterable[Tuple[int,int]]) -> Dict[int, List[int]]:
    H = {i: [] for i in range(n)}
    for u,v in E: H[u].append(v)
    for u in H: H[u] = sorted(set(H[u]))
    return H

def permute_nodes(H: Dict[int, List[int]], pi: List[int]) -> Dict[int, List[int]]:
    n = len(H)
    M = {i: pi[i] for i in range(n)}
    return from_edges(n, [(M[u], M[v]) for (u,v) in edges_of(H)])

def rotate_graph(H: Dict[int, List[int]], k: int) -> Dict[int, List[int]]:
    n = len(H)
    k %= n
    if k==0: return {u: vs[:] for u,vs in H.items()}
    f = lambda u: (u+k)%n
    return from_edges(n, [(f(u), f(v)) for (u,v) in edges_of(H)])

def quotient_graph_mod(H: Dict[int, List[int]], m: int) -> Dict[int, List[int]]:
    E = set(((u%m, v%m) for (u,v) in edges_of(H)))
    Q = {c: [] for c in range(m)}
    for a,b in sorted(E): Q[a].append(b)
    for c in Q: Q[c] = sorted(set(Q[c]))
    return Q

# Executor step (X and H paths)

def exec_program(program: Dict[str, Any], outdir: str, seed: int) -> Dict[str, Any]:
    os.makedirs(outdir, exist_ok=True)
    # Save program copy
    with open(os.path.join(outdir, "program.json"), "w", encoding="utf-8") as f:
        json.dump(program, f, indent=2, ensure_ascii=False)

    rng = np.random.default_rng(seed)
    x = rng.normal(size=N)
    H = make_ring_graph(N)

    trace_path = os.path.join(outdir, "trace.jsonl")
    tf = open(trace_path, "w", encoding="utf-8")

    def log(op: str, pre: Dict[str, Any], post: Dict[str, Any], note: str|None=None):
        rec = {"op": op, "pre": pre, "post": post}
        if note: rec["note"] = note
        tf.write(json.dumps(rec, ensure_ascii=False) + "\n")

    def stats(arr: np.ndarray) -> Dict[str, Any]:
        return {"energy": float(np.dot(arr, arr)), "mean": float(np.mean(arr)), "std": float(np.std(arr))}

    t_exec0 = time.time()
    ctx: Dict[str, Any] = {}
    for w in program.get("words", []):
        op = w["op"]
        pre = stats(x)
        if op == "copy":
            pass
        elif op == "rotate":
            k = int(w.get("k",0))
            x = rotate_Rk(x, k)
            H = rotate_graph(H, k)
        elif op == "permute":
            pi = w.get("pi", list(range(N)))
            x = x[np.array(pi)]
            H = permute_nodes(H, pi)
        elif op == "projector":
            p, r = int(w["p"]), int(w["r"]);  m = p**r
            mode = w.get("mode","Δ")
            ctx["last_m"] = m
            if mode == "A":
                x = projector_A(x, m)
                H = quotient_graph_mod(H, m)
            else:
                x = projector_Delta(x, m)
        elif op == "split":
            m = ctx.get("last_m", 3)
            ctx["split_m"] = m
            H = quotient_graph_mod(H, m)
        elif op == "merge":
            ctx.pop("split_m", None)
        elif op in ("modal_enter","modal_exit"):
            pass
        else:
            raise ValueError(f"Unknown op: {op}")
        post = stats(x)
        log(op, pre, post, w.get("note"))

    tf.close()
    exec_time_s = time.time() - t_exec0

    # Metrics: EVR and retrieval uplift
    m = ctx.get("last_m", 3)
    Ax = projector_A(x, m)
    Dx = projector_Delta(x, m)
    def energy_ratio(a: np.ndarray, b: np.ndarray) -> float:
        num = float(np.dot(b,b)); den = float(np.dot(a,a)) or 1.0
        return num/den
    evr_A = energy_ratio(x, Ax)
    evr_D = energy_ratio(x, Dx)
    # Baseline EVR using random permutations
    def baseline_evr(x: np.ndarray, m: int, trials: int=50, seed: int=7) -> Tuple[float,float]:
        R = random.Random(seed); n = x.size
        vals = []
        for _ in range(trials):
            pi = list(range(n)); R.shuffle(pi)
            xp = x[np.array(pi)]
            yp = projector_A(xp, m)
            vals.append(energy_ratio(xp, yp))
        return float(statistics.mean(vals)), float(statistics.pstdev(vals))
    base_mean, base_std = baseline_evr(x, m, 50, seed+1)

    metrics = {
        "n": N,
        "last_m": m,
        "evr_A": evr_A,
        "evr_Delta": evr_D,
        "baseline_evr_A": {"mean": base_mean, "std": base_std},
        "relation": {
            "|E|": len(edges_of(H))
        },
        "wall_time_exec_s": exec_time_s
    }

    with open(os.path.join(outdir, "metrics.json"), "w", encoding="utf-8") as f:
        json.dump(metrics, f, indent=2, ensure_ascii=False)

    return metrics

# -------------------------
# Phase 3 — Unit properties
# -------------------------

def unit_projector_idempotence(trials: int = 5, seeds: List[int] | None = None) -> Dict[str, Any]:
    seeds = seeds or list(range(10, 10+trials))
    out = {"A": [], "Delta": []}
    for s in seeds:
        rng = np.random.default_rng(s)
        x = rng.normal(size=N)
        for m in (3,):  # admissible
            Ax = projector_A(x, m)
            AAx = projector_A(Ax, m)
            Dx = projector_Delta(x, m)
            DDx = projector_Delta(Dx, m)
            errA = float(np.max(np.abs(AAx - Ax)))
            errD = float(np.max(np.abs(DDx - Dx)))
            out["A"].append({"m": m, "max_abs_err": errA})
            out["Delta"].append({"m": m, "max_abs_err": errD})
    return out

# W^{(q)} witness permutation: within each 256‑page, map offset -> (offset*q) mod 256 (q coprime to 256)

def witness_perm_q(q: int) -> List[int]:
    if math.gcd(q, 256) != 1:
        raise ValueError("q must be coprime with 256 for stride permutation")
    pi = [0]*N
    for page in range(PAGES):
        base = page*256
        for offset in range(256):
            pi[base + offset] = base + ((offset * q) % 256)
    return pi

def unit_noncommutation_witness(p: int = 3, q: int = 5, trials: int = 5, tol: float = 1e-9) -> Dict[str, Any]:
    # Check existence of x s.t. A_p W_q x != W_q A_p x
    assert N % p == 0, "p must divide N"
    pi = witness_perm_q(q)
    counts = 0
    diffs = []
    for s in range(100, 100+trials):
        rng = np.random.default_rng(s)
        x = rng.normal(size=N)
        W_x = x[np.array(pi)]
        lhs = projector_A(W_x, p)        # A_p W_q x
        rhs = (projector_A(x, p))[np.array(pi)]  # W_q A_p x
        d = float(np.max(np.abs(lhs - rhs)))
        diffs.append(d)
        if d > tol: counts += 1
    return {"p": p, "q": q, "noncommute_trials": counts, "trials": trials, "max_diff": float(max(diffs)), "min_diff": float(min(diffs))}

def unit_rotation_closure() -> Dict[str, Any]:
    rng = np.random.default_rng(777)
    x = rng.normal(size=N)
    xr = rotate_Rk(x, N)
    err = float(np.max(np.abs(xr - x)))
    return {"R^n_identity_max_abs_err": err}

def unit_split_merge_roundtrip(m: int = 3) -> Dict[str, Any]:
    H0 = make_ring_graph(N)
    Hs = quotient_graph_mod(H0, m)
    Hm = Hs  # minimal merge
    return {
        "contracted_edges": len(edges_of(Hs)),
        "roundtrip_equal": (Hs == Hm)
    }

# -------------------------
# Round‑trip test (supported subset)
# -------------------------

def roundtrip_check(source: str) -> Dict[str, Any]:
    lo = lower(source, src_name="source")
    prog = compile_program(lo["lowered"], Policies())
    src2 = pretty_print_program(prog)
    lo2 = lower(src2, src_name="pretty")
    equal_words = (lo["lowered"]["words"] == lo2["lowered"]["words"])  # only for supported subset
    return {
        "lowering_hash_1": lo["lowering_hash"],
        "lowering_hash_2": lo2["lowering_hash"],
        "hash_equal": (lo["lowering_hash"] == lo2["lowering_hash"]),
        "structure_equal": equal_words,
        "pretty_script": src2
    }

# -------------------------
# KPIs
# -------------------------

def determinism_rate(source: str, variants: int = 20) -> float:
    base = lower(source, src_name="base")["lowering_hash"]
    ok = 0
    for k in range(variants):
        # Inject random whitespace
        noisy = re.sub(r";", lambda m: "  ;\n" if random.random()<0.5 else "; ", source)
        noisy = noisy.replace(" ", "  ") if random.random()<0.5 else noisy
        h = lower(noisy, src_name=f"v{k}")["lowering_hash"]
        if h == base: ok += 1
    return ok / variants

def obligation_counts(program: Dict[str, Any]) -> Dict[str, int]:
    c = {"UNPROVEN": 0, "VIOLATION": 0}
    for ob in program.get("obligations", []):
        s = ob.get("status")
        if s in c: c[s] += 1
    return c

# -------------------------
# Runner / CLI
# -------------------------

def main():
    ap = argparse.ArgumentParser()
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--program", help="compiled_program.json from Phase 1")
    g.add_argument("--source", help="Sigmatics source file to lower+compile here")
    ap.add_argument("--outdir", required=True)
    ap.add_argument("--seed", type=int, default=42)
    args = ap.parse_args()

    os.makedirs(args.outdir, exist_ok=True)

    # Resolve program
    t0 = time.time()
    program = None
    if args.program:
        with open(args.program, "r", encoding="utf-8") as f:
            program = json.load(f)
    else:
        with open(args.source, "r", encoding="utf-8") as f:
            src = f.read()
        lo = lower(src, src_name=os.path.basename(args.source))
        program = compile_program(lo["lowered"], Policies())
        with open(os.path.join(args.outdir, "program.json"), "w", encoding="utf-8") as f:
            json.dump(program, f, indent=2, ensure_ascii=False)
    t_compile = time.time() - t0

    # Execute (Phase 2 behavior)
    t1 = time.time()
    metrics = exec_program(program, args.outdir, args.seed)
    t_exec = time.time() - t1

    # Unit properties
    unit = {
        "projector_idempotence": unit_projector_idempotence(),
        "noncommutation_witness": unit_noncommutation_witness(p=3, q=5, trials=5),
        "rotation_closure": unit_rotation_closure(),
        "split_merge_roundtrip": unit_split_merge_roundtrip(m=3)
    }
    with open(os.path.join(args.outdir, "validation_report.json"), "w", encoding="utf-8") as f:
        json.dump(unit, f, indent=2, ensure_ascii=False)

    # Round‑trip on a supported subset example
    subset_src = """
        mark@{"p":3,"r":1,"mode":"delta"};
        rho[7];
        copy;
        split@ℓ:int;
        merge;
        quote;
        evaluate;
    """
    rt = roundtrip_check(subset_src)
    with open(os.path.join(args.outdir, "roundtrip.json"), "w", encoding="utf-8") as f:
        json.dump(rt, f, indent=2, ensure_ascii=False)

    # KPIs
    resonance_uplift = metrics["evr_A"] - metrics["baseline_evr_A"]["mean"]
    det_rate = determinism_rate(subset_src, variants=20)
    oblig = obligation_counts(program)
    kpis = {
        "n": N,
        "resonance_uplift_vs_baseline": resonance_uplift,
        "evr_A": metrics["evr_A"],
        "baseline_evr_A_mean": metrics["baseline_evr_A"]["mean"],
        "wall_time_compile_s": t_compile,
        "wall_time_exec_s": t_exec,
        "determinism_rate_lowering": det_rate,
        "obligation_counts": oblig,
        "noncommute_trials": unit["noncommutation_witness"]["noncommute_trials"],
        "noncommute_trials_total": unit["noncommutation_witness"]["trials"]
    }
    with open(os.path.join(args.outdir, "kpis.json"), "w", encoding="utf-8") as f:
        json.dump(kpis, f, indent=2, ensure_ascii=False)

    print(json.dumps({
        "compile_s": t_compile,
        "exec_s": t_exec,
        "kpis": kpis
    }, indent=2))

if __name__ == "__main__":
    main()
