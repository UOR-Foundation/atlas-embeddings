import json
import sys

from atlas.aep.decision_rules import AEP, DEFAULT_PREDICATES, launch


class DummyKernel:
    def eval(self, ctx):
        return {"ok": True}


def main() -> None:
    aep_json = json.load(sys.stdin)
    aep = AEP(
        C=aep_json["C"],
        K=DummyKernel(),
        W=aep_json["W"],
        theta=aep_json.get("theta", {}),
    )
    attrs = {"claims": aep_json["C"]}
    decision = launch(aep, DEFAULT_PREDICATES, attrs)
    print(
        json.dumps(
            {
                "status": decision.status,
                "code": decision.code,
                "reason": decision.reason,
                "evidence": decision.evidence,
                "log": decision.log,
            },
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
