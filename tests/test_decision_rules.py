from atlas.aep.decision_rules import AEP, DEFAULT_PREDICATES, launch


class K:
    def eval(self, ctx):
        return {"ok": True}


def test_pass_unity_neutral_delta_zero():
    aep = AEP(
        C=["unity_neutral"],
        K=K(),
        W={"delta_R": [0, 0, 0]},
        theta={},
    )
    attrs = {"claims": ["unity_neutral"]}
    decision = launch(aep, DEFAULT_PREDICATES, attrs)
    assert decision.status == "PASS" and decision.code == 0


def test_fault_unity_neutral_unresolved():
    aep = AEP(
        C=["unity_neutral"],
        K=K(),
        W={"delta_R": [1, 0, 0]},
        theta={},
    )
    attrs = {"claims": ["unity_neutral"]}
    decision = launch(aep, DEFAULT_PREDICATES, attrs)
    assert decision.status == "FAULT" and decision.code == 2001
