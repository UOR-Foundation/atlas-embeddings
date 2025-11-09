import os, json, numpy as np
from runner.metrics import spectral_bounds, neumann_tail_bound
from runner.monitors import monitor_tick
from atlas.ace.projection import project_dual
from atlas.ace.norms import build_K

def build_operator(weights, basis):
    return build_K([np.asarray(B,float) for B in basis], np.asarray(weights,float))

def deterministic_runner(seed, dtype, rmode):
    os.environ["PYTHONHASHSEED"]=str(seed)
    np.random.seed(seed)
    # dtype/rmode plumbed into kernels as needed
    return {"seed":seed,"dtype":dtype,"rmode":rmode}

def run(aep_cfg_json, basis, F, x0, w_tilde, b, a, eps, tau, tailspec, window_pred, kernel_eval, conjugator, probes, R_pre, R_post, delta_R=None):
    # projection
    w_star, diag = project_dual(np.asarray(w_tilde,float), np.asarray(b,float), np.asarray(a,float), eps, tau)
    # operator + bounds
    K = build_operator(w_star, basis)
    rho_hat, norm_hat = spectral_bounds(K)
    gapLB = 1.0 - rho_hat
    slopeUB = norm_hat
    # monitors
    state = {"x": np.asarray(x0,float)}
    state = monitor_tick(state, K, np.asarray(F,float), state["x"], gapLB, slopeUB, tailspec)
    # witnesses
    from runner.witness_checks import check_unity_neutral, check_mirror_safe, check_boundaries, check_phase
    ok_u, ev_u = check_unity_neutral(R_pre, R_post, delta_R)
    ok_b, ev_b = check_boundaries(probes["footprint"], window_pred)
    ok_p, ev_p = check_phase(probes["phase"], aep_cfg_json["claims"]["phase_window"]["phi0"], aep_cfg_json["claims"]["phase_window"]["span"])
    ok_m, ev_m = check_mirror_safe(kernel_eval, conjugator, probes["mirror"])

    evidence = {
        "projection":{"w_star": w_star.tolist(), **diag},
        "bounds":{"rho_hat":rho_hat, "slopeUB":slopeUB, "gapLB":gapLB},
        "monitor": state["status"],
        "witness":{"unity_neutral":ev_u,"boundary":ev_b,"phase":ev_p,"mirror":ev_m}
    }
    ok = (gapLB>float(aep_cfg_json["ace"].get("GapLB_min",0))) and (slopeUB<float(aep_cfg_json["ace"].get("SlopeUB_max",1))) and ok_u and ok_b and ok_p and ok_m
    return ok, evidence

if __name__=="__main__":
    cfg = json.load(open("aep.json","r"))
    ok, ev = run(**cfg)
    print(json.dumps({"ok":ok, "evidence":ev}, indent=2))
    raise SystemExit(0 if ok else 160)
