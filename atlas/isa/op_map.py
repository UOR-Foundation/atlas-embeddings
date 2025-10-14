from __future__ import annotations
from dataclasses import dataclass, field
from typing import Dict, Any, List
import os, json, hashlib

from atlas.aep.claims_attrs_witnesses import prepare_claims_attrs_witness, load_aep_toml
from atlas.aep.ace import Budgets, project_dual_int
from atlas.aep.petc import (
    verify_freeness_sample, verify_orbit_counts, verify_C768_closure, verify_phi_equivariance_sample,
    PETCLedger, ChannelRow
)
from atlas.aep.pi_adapter import ChannelDef, PiAtom, PiConfig, pi_runtime_step
from atlas.aep.pirtm import monitor_step

# ---------------------------
# ISA context
# ---------------------------

@dataclass
class ISAContext:
    Q: int = 10**6
    aep_toml_path: str = ""
    attrs: Dict[str, Any] = field(default_factory=dict)
    kernel_attrs: Dict[str, Any] = field(default_factory=dict)
    W: Dict[str, Any] = field(default_factory=dict)
    proj: Dict[str, Any] = field(default_factory=dict)
    channels: Dict[str, ChannelDef] = field(default_factory=dict)
    ledger: PETCLedger = field(default_factory=PETCLedger)
    step: Any = None
    monitor: Any = None
    evidence: Dict[str, Any] = field(default_factory=dict)
    snap_id: str = ""

# ---------------------------
# ISA ops
# ---------------------------

def op_SCHEMA(ctx: ISAContext, typ: str, aep_toml: str) -> None:
    if typ != "AEP":
        raise ValueError("unsupported schema type")
    _ = load_aep_toml(aep_toml)  # validates
    ctx.aep_toml_path = aep_toml

def op_NEW(ctx: ISAContext, typ: str, aep_toml: str) -> None:
    if typ != "AEP":
        raise ValueError("unsupported NEW type")
    ctx.aep_toml_path = aep_toml
    # defer attrs until IMPORT(W)

def op_TAG(ctx: ISAContext, attrs: Dict[str, Any]) -> None:
    # attach or override kernel attrs
    for k,v in attrs.items():
        ctx.kernel_attrs[k] = v

def op_IMPORT_witness(ctx: ISAContext, witness_path: str) -> None:
    W_in = json.load(open(witness_path, "r"))
    theta = {"Q": ctx.Q}
    attrs_dict, kernel_attrs, W = prepare_claims_attrs_witness(ctx.aep_toml_path, W_in, theta)
    ctx.attrs = attrs_dict
    ctx.kernel_attrs.update(kernel_attrs)
    ctx.W = W

def op_MAP_project_dual(ctx: ISAContext, wtilde_Q: List[int], b: List[int], a: List[int], limit1_Q: int, limit2_Q: int) -> None:
    budgets = Budgets(b=b, a=a, limit1_Q=limit1_Q, limit2_Q=limit2_Q, Q=ctx.Q)
    proj = project_dual_int(wtilde_Q, budgets)
    ctx.proj = {
        "w_star_Q": proj.w_star_Q, "lam_Q": proj.lam_Q, "mu_Q": proj.mu_Q,
        "sum1": proj.sum1, "sum2": proj.sum2, "iters": getattr(proj, "iters", 0)
    }

def op_ASSERT_PETC(ctx: ISAContext) -> None:
    if not verify_freeness_sample():           raise RuntimeError("PETC freeness failed")
    if not verify_orbit_counts():              raise RuntimeError("PETC orbit counts failed")
    if not verify_C768_closure():              raise RuntimeError("PETC C768 closure failed")
    if not verify_phi_equivariance_sample():   raise RuntimeError("PETC Phi-equivariance failed")

def _mv_scale(Q: int, k_num: int):
    def mv(v: List[int]) -> List[int]:
        return [(k_num * x) // Q for x in v]
    return mv

def op_EVAL_step(
    ctx: ISAContext,
    channels_cfg: List[Dict[str, Any]],
    ledger_cfg: List[Dict[str, Any]],
    F_Q: List[int],
    T_Q: List[int],
) -> None:
    # build channels
    ch: Dict[str, ChannelDef] = {}
    for c in channels_cfg:
        cid = str(c["id"])
        norm_Q = int(c["norm_Q"])
        ch[cid] = ChannelDef(
            id=cid,
            sigma=c.get("sigma", {}),
            commutator_class=str(c.get("class", "X")),
            B_norm_Q=norm_Q,
            B_matvec=_mv_scale(ctx.Q, norm_Q)
        )
    ctx.channels = ch
    # build ledger
    L = PETCLedger()
    for c in ledger_cfg:
        cls = str(c["class"])
        bud = int(c["budget"])
        cid = f"seed_{cls}"
        L.add_channel(ChannelRow(id=cid, sigma={}, budget=bud, commutator_class=cls))
    ctx.ledger = L
    # atoms from projection result or zero
    w_map = {}
    if ctx.proj:
        # align order with channels_cfg
        wv = ctx.proj["w_star_Q"]
        for i, c in enumerate(channels_cfg):
            w_map[str(c["id"])] = int(wv[i] if i < len(wv) else 0)
    atoms = [PiAtom(id=f"a_{i}", channel_id=str(c["id"]), wtilde_Q=int(w_map.get(str(c["id"]), 0))) for i, c in enumerate(channels_cfg)]
    cfg = PiConfig(Q=ctx.Q, budgets=Budgets(
        b=[1]*len(channels_cfg), a=[1]*len(channels_cfg),
        limit1_Q=ctx.Q, limit2_Q=ctx.Q, Q=ctx.Q
    ), dim=len(F_Q))
    step = pi_runtime_step(atoms, ch, cfg, L, F_Q, T_Q, rho_hat_scaled_opt=None)
    ctx.step = step

def op_REDUCE_norm_est(ctx: ISAContext, N: int, threshold_Q: int) -> None:
    # conservative scalar K using max channel norm
    norms = [ctx.channels[cid].B_norm_Q for cid in ctx.channels] if ctx.channels else [0]
    k_eff = max(norms) if norms else 0
    def K(v: List[int]) -> List[int]:
        return [(k_eff * x) // ctx.Q for x in v]
    F_Q = [0]*len(ctx.step.T_next) if ctx.step else [0]
    v_power = [ctx.Q] + [0]*(len(F_Q)-1)
    ctx.monitor = monitor_step(K, F_Q, v_power, ctx.Q, N=N, threshold_Q=threshold_Q, sig_history=[{2:1},{2:1}])

def op_ASSERT_gap_slope(ctx: ISAContext) -> None:
    if ctx.step is None:
        raise RuntimeError("no step to assert")
    slope_s = int(ctx.step.slope_scaled)
    gap_s = int(ctx.step.gap_scaled)
    Q2 = ctx.Q * ctx.Q
    if not (slope_s < Q2):  raise RuntimeError("SlopeUB>=1")
    if not (gap_s > 0):     raise RuntimeError("GapLB<=0")
    if ctx.monitor is not None:
        if not (ctx.monitor.norm_hat_Q < ctx.Q): raise RuntimeError("||K||_hat>=1")

def op_AUDIT_evidence(ctx: ISAContext) -> None:
    payload = {
        "claims": ctx.attrs.get("claims", []),
        "delta_R": ctx.W.get("delta_R", []),
        "w_star_map_Q": getattr(ctx.step, "w_star_map_Q", {}),
        "used_channels": getattr(ctx.step.audit, "used_channels", []),
        "budgets": getattr(ctx.step.audit, "petc_budgets", {}),
        "norm_hat_Q": getattr(ctx.monitor, "norm_hat_Q", None),
        "gap_lb_Q": getattr(ctx.monitor, "gap_lb_Q", None),
    }
    j = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    ctx.evidence = {"digest_hex": hashlib.sha256(j.encode("utf-8")).hexdigest(), "payload": payload}

def op_SNAP(ctx: ISAContext) -> None:
    snap_src = json.dumps({
        "attrs": ctx.attrs, "W_keys": sorted(ctx.W.keys()),
        "proj": ctx.proj, "used": getattr(ctx.step.audit, "used_channels", []) if ctx.step else []
    }, sort_keys=True, separators=(",", ":"))
    ctx.snap_id = hashlib.sha256(snap_src.encode("utf-8")).hexdigest()

def op_EXPORT_report(ctx: ISAContext, path: str) -> None:
    os.makedirs(os.path.dirname(path), exist_ok=True)
    out = {
        "Q": ctx.Q,
        "snap_id": ctx.snap_id,
        "attrs": ctx.attrs,
        "kernel_attrs": ctx.kernel_attrs,
        "evidence": ctx.evidence,
        "step_ok": bool(getattr(ctx.step, "accepted", False)),
        "monitor": ctx.monitor.__dict__ if ctx.monitor else {},
    }
    with open(path, "w") as f:
        json.dump(out, f, indent=2, sort_keys=True)

# ---------------------------
# Pipeline runner
# ---------------------------

def run_pipeline(ops: List[Dict[str, Any]], Q: int = 10**6) -> ISAContext:
    ctx = ISAContext(Q=Q)
    for op in ops:
        kind = op["op"]
        if kind == "SCHEMA":
            op_SCHEMA(ctx, op["type"], op["aep_toml"])
        elif kind == "NEW":
            op_NEW(ctx, op["type"], op["aep_toml"])
        elif kind == "TAG":
            op_TAG(ctx, op.get("attrs", {}))
        elif kind == "IMPORT":
            if op["what"] != "witness": raise ValueError("unsupported IMPORT")
            op_IMPORT_witness(ctx, op["path"])
        elif kind == "MAP":
            if op["fn"] != "project_dual": raise ValueError("unsupported MAP")
            op_MAP_project_dual(ctx, op["wtilde_Q"], op["b"], op["a"], int(op["limit1_Q"]), int(op["limit2_Q"]))
        elif kind == "ASSERT":
            what = op["what"]
            if what == "PETC": op_ASSERT_PETC(ctx)
            elif what == "gap_slope": op_ASSERT_gap_slope(ctx)
            else: raise ValueError("unsupported ASSERT")
        elif kind == "EVAL":
            if op["what"] != "step": raise ValueError("unsupported EVAL")
            op_EVAL_step(ctx, op["channels"], op["ledger"], op["F_Q"], op["T_Q"])
        elif kind == "REDUCE":
            if op["what"] != "norm_est": raise ValueError("unsupported REDUCE")
            op_REDUCE_norm_est(ctx, int(op.get("N", 3)), int(op.get("threshold_Q", ctx.Q // 10)))
        elif kind == "AUDIT":
            if op["what"] != "evidence": raise ValueError("unsupported AUDIT")
            op_AUDIT_evidence(ctx)
        elif kind == "SNAP":
            op_SNAP(ctx)
        elif kind == "EXPORT":
            if op["what"] != "report": raise ValueError("unsupported EXPORT")
            op_EXPORT_report(ctx, op["path"])
        else:
            raise ValueError(f"unknown op: {kind}")
    return ctx
