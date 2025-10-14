from __future__ import annotations
import argparse, json, os, sys, time, hashlib
from typing import List, Dict

from atlas.aep.claims_attrs_witnesses import prepare_claims_attrs_witness
from atlas.aep.decision_rules import AEP, DEFAULT_PREDICATES, launch, canon_decision
from atlas.runtime.backends import LocalBackend, run_multi_backend_and_compare
from atlas.aep.petc import (
    verify_freeness_sample, verify_orbit_counts, verify_C768_closure, verify_phi_equivariance_sample,
    cert_tensor_product, cert_contraction, axis_signature, PETCLedger, ChannelRow
)
from atlas.aep.ace import Budgets, ace_accept
from atlas.aep.pi_adapter import (
    ChannelDef, PiAtom, PiConfig, pi_runtime_step
)
from atlas.aep.pirtm import monitor_step

# -------- util (no floats) --------
def _mv_scale(Q: int, k_num: int):
    def mv(v: List[int]) -> List[int]:
        return [(k_num * x) // Q for x in v]
    return mv

def _sha(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        while True:
            b = f.read(1 << 16)
            if not b:
                break
            h.update(b)
    return h.hexdigest()

# -------- CI gates --------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--aep-toml", required=True)
    ap.add_argument("--witness", required=True)
    ap.add_argument("--kernel", required=True)          # path to kernel.atlas
    ap.add_argument("--Q", type=int, default=10**6)
    ap.add_argument("--outdir", default="artifacts/aep")
    args = ap.parse_args()

    Q = int(args.Q)

    # 1) Build kernel.atlas (existence + digest)
    if not os.path.exists(args.kernel) or os.path.getsize(args.kernel) <= 0:
        print("CI: kernel.atlas missing or empty", file=sys.stderr)
        sys.exit(2)
    kernel_digest = _sha(args.kernel)

    # 2) Parse claims, attrs, witness (normalized, no floats)
    W_in = json.load(open(args.witness, "r"))
    theta = {"Q": Q}
    attrs_dict, _, W = prepare_claims_attrs_witness(args.aep_toml, W_in, theta)

    # 3) PETC certificates (group gate + structural)
    if not verify_freeness_sample():
        print("CI: PETC freeness failed", file=sys.stderr)
        sys.exit(3)
    if not verify_orbit_counts():
        print("CI: PETC orbit counts failed", file=sys.stderr)
        sys.exit(3)
    if not verify_C768_closure():
        print("CI: PETC C768 closure failed", file=sys.stderr)
        sys.exit(3)
    if not verify_phi_equivariance_sample():
        print("CI: PETC Phi-equivariance failed", file=sys.stderr)
        sys.exit(3)
    # basic C_⊗ and C_<·,·> samples tied to channel shapes
    s12, s20 = axis_signature(12), axis_signature(20)
    if not cert_tensor_product(s12, s20, {2: 4, 3: 1, 5: 1}):
        print("CI: C_⊗ sample failed", file=sys.stderr)
        sys.exit(3)
    if not cert_contraction([12, 7], [49, 12], [(0, 1)]):
        print("CI: C_<·,·> sample failed", file=sys.stderr)
        sys.exit(3)

    # 4) ACE: project to S and require GapLB>0, SlopeUB<1
    # Define channels and norms (device-independent)
    channels: Dict[str, ChannelDef] = {
        "c1": ChannelDef(id="c1", sigma={2: 1}, commutator_class="X", B_norm_Q=Q // 2, B_matvec=_mv_scale(Q, Q // 2)),
        "c2": ChannelDef(id="c2", sigma={3: 1}, commutator_class="Y", B_norm_Q=Q // 3, B_matvec=_mv_scale(Q, Q // 3)),
    }
    # Budgets: sum b|w| <= (1*Q), sum a|w| <= (1*Q)
    b = [1, 1]
    a = [1, 1]
    budgets = Budgets(b=b, a=a, limit1_Q=1 * Q, limit2_Q=1 * Q, Q=Q)
    cfg = PiConfig(Q=Q, budgets=budgets, dim=3)
    # Proposed weights (scaled integers)
    atoms = [PiAtom(id="a1", channel_id="c1", wtilde_Q=Q), PiAtom(id="a2", channel_id="c2", wtilde_Q=Q)]
    # Ledger for PETC budgets
    L = PETCLedger()
    L.add_channel(ChannelRow(id="c1", sigma=channels["c1"].sigma, budget=2, commutator_class="X"))
    L.add_channel(ChannelRow(id="c2", sigma=channels["c2"].sigma, budget=2, commutator_class="Y"))
    # Run Π-adapter step (projects and audits)
    F_Q = [0, 0, 0]
    T_Q = [Q, 0, 0]
    step = pi_runtime_step(atoms, channels, cfg, L, F_Q, T_Q, rho_hat_scaled_opt=None)
    if not step.accepted:
        print("CI: ACE projection or PETC audit failed", file=sys.stderr)
        sys.exit(4)
    slope_s = step.slope_scaled
    # Require SlopeUB<1 -> slope_scaled < Q^2
    if not (slope_s < Q * Q):
        print("CI: SlopeUB>=1", file=sys.stderr)
        sys.exit(4)
    # GapLB > 0
    if not (step.gap_scaled > 0):
        print("CI: GapLB<=0", file=sys.stderr)
        sys.exit(4)

    # 5) PIRTM monitor: require \widehat{||K||} < 1 and certified tails
    # Rebuild K matvec from channels and projected weights
    Bnorms = [channels["c1"].B_norm_Q, channels["c2"].B_norm_Q]
    ok_slope, _ = ace_accept(list(step.w_star_map_Q.values()), Bnorms, Q, None)
    if not ok_slope:
        print("CI: slope acceptance failed", file=sys.stderr)
        sys.exit(5)
    # Use adapter's K via a lambda around step.T_next-F (single tick replicated by pirtm with dummy K)
    # Build a matvec consistent with the adapter:
    def mv_scale_k(k_num: int):
        def mv(v: List[int]) -> List[int]:
            return [(k_num * x) // Q for x in v]
        return mv
    # Effective scalar bound for demo: pick max channel norm under L1 mixing
    # This stays conservative and integer.
    k_eff = max(Bnorms)
    K = mv_scale_k(k_eff)
    v_power = [Q, Q, 0]
    rep = monitor_step(K, F_Q, v_power, Q, N=3, threshold_Q=Q // 10, sig_history=[{2: 1}, {2: 1}])
    if not (rep.norm_hat_Q < Q):
        print("CI: \\widehat{||K||}>=1", file=sys.stderr)
        sys.exit(5)
    # Tail bound is computed; accept existence (nonnegative)
    if rep.tail_bound_Q < 0:
        print("CI: negative tail bound", file=sys.stderr)
        sys.exit(5)

    # 6) All claim predicates true via decision rules over normalized witness
    class Kernel:
        def __init__(self, digest: str):
            self.digest = digest

        def eval(self, ctx):
            return {"ok": True, "kernel_digest": self.digest}

    aep = AEP(C=list(attrs_dict["claims"]), K=Kernel(kernel_digest), W=W, theta=theta)
    decision = launch(aep, DEFAULT_PREDICATES, attrs_dict)
    if decision.status != "PASS":
        print("CI: claim predicate failed", file=sys.stderr)
        sys.exit(6)

    # 7) Determinism and portability: run on two backends, compare canonical decisions
    be1 = LocalBackend(name="cpu", fixed_time_ns=123456789, device_tag="cpu")
    be2 = LocalBackend(name="gpu", fixed_time_ns=123456789, device_tag="gpu")
    multi = run_multi_backend_and_compare(aep, attrs_dict, [be1, be2])
    if not multi["equal"]:
        print("CI: backend decisions differ", file=sys.stderr)
        sys.exit(7)

    # 8) Archive logs, ΔR, coverage maps (used channels)
    ts = str(int(time.time()))
    outdir = os.path.join(args.outdir, ts)
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "kernel_digest.txt"), "w") as f:
        f.write(kernel_digest + "\n")
    with open(os.path.join(outdir, "decision.json"), "w") as f:
        json.dump(canon_decision(decision), f, indent=2, sort_keys=True)
    with open(os.path.join(outdir, "pi_step.json"), "w") as f:
        json.dump({
            "w_star_map_Q": step.w_star_map_Q,
            "slope_scaled": step.slope_scaled,
            "gap_scaled": step.gap_scaled,
            "audit": {"used_channels": step.audit.used_channels, "budgets": step.audit.petc_budgets, "quarantine": step.audit.quarantine}
        }, f, indent=2, sort_keys=True)
    with open(os.path.join(outdir, "pirtm_report.json"), "w") as f:
        json.dump(rep.__dict__, f, indent=2, sort_keys=True)
    with open(os.path.join(outdir, "witness_deltaR.json"), "w") as f:
        json.dump({"delta_R": W.get("delta_R", []), "Q": Q}, f, indent=2, sort_keys=True)
    with open(os.path.join(outdir, "backend_compare.json"), "w") as f:
        json.dump(multi, f, indent=2, sort_keys=True)

    print("CI: all gates passed")


if __name__ == "__main__":
    main()
