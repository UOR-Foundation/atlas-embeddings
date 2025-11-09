import argparse
import json
import sys

from atlas.aep.claims_attrs_witnesses import prepare_claims_attrs_witness
from atlas.aep.decision_rules import AEP, DEFAULT_PREDICATES, launch


class DummyKernel:
    def __init__(self, attrs: dict) -> None:
        self.attrs = attrs

    def eval(self, ctx):
        return {"ok": True, "attrs": self.attrs}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--aep-toml", required=True)
    args = parser.parse_args()

    aep_json = json.load(sys.stdin)
    theta = aep_json.get("theta", {})
    attrs, kernel_attrs, witness = prepare_claims_attrs_witness(
        args.aep_toml, aep_json["W"], theta
    )

    aep = AEP(
        C=attrs["claims"],
        K=DummyKernel(kernel_attrs),
        W=witness,
        theta=theta,
    )
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
