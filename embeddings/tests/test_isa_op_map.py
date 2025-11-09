import os, json
from atlas.isa.op_map import run_pipeline

Q = 10**6

def test_full_pipeline_minimal():
    report_path = "artifacts/isa/report.json"
    ops = [
        {"op":"SCHEMA","type":"AEP","aep_toml":"examples/aep_unity_neutral/aep.toml"},
        {"op":"NEW","type":"AEP","aep_toml":"examples/aep_unity_neutral/aep.toml"},
        {"op":"IMPORT","what":"witness","path":"examples/aep_unity_neutral/witness.json"},
        {"op":"MAP","fn":"project_dual","wtilde_Q":[Q,Q],"b":[1,1],"a":[1,1],"limit1_Q":Q,"limit2_Q":Q},
        {"op":"ASSERT","what":"PETC"},
        {
            "op":"EVAL","what":"step",
            "channels":[
                {"id":"c1","norm_Q":Q//2,"class":"X"},
                {"id":"c2","norm_Q":Q//3,"class":"Y"}
            ],
            "ledger":[{"class":"X","budget":2},{"class":"Y","budget":2}],
            "F_Q":[0,0,0],
            "T_Q":[Q,0,0]
        },
        {"op":"REDUCE","what":"norm_est","N":3,"threshold_Q":Q//10},
        {"op":"ASSERT","what":"gap_slope"},
        {"op":"AUDIT","what":"evidence"},
        {"op":"SNAP"},
        {"op":"EXPORT","what":"report","path":report_path}
    ]
    ctx = run_pipeline(ops, Q=Q)
    assert ctx.step and ctx.step.accepted
    assert ctx.monitor and ctx.monitor.norm_hat_Q < Q
    assert ctx.snap_id and len(ctx.snap_id) > 0
    assert os.path.exists(report_path)
    data = json.load(open(report_path,"r"))
    assert data["Q"] == Q and data["step_ok"] is True
