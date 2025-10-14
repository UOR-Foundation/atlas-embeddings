from __future__ import annotations
from dataclasses import dataclass
from typing import Dict, Any, Protocol, Tuple, List
import json

from atlas.aep.decision_rules import (
    AEP,
    DEFAULT_PREDICATES,
    launch,
    set_clock_ns,
    canon_decision,
)


class Backend(Protocol):
    name: str

    def legalize(self, aep: AEP, attrs: Dict[str, Any]) -> Tuple[AEP, Dict[str, Any]]:
        ...

    def monotone_clock_ns(self) -> int:
        ...


@dataclass(frozen=True)
class LocalBackend:
    name: str
    fixed_time_ns: int
    device_tag: str

    def legalize(self, aep: AEP, attrs: Dict[str, Any]) -> Tuple[AEP, Dict[str, Any]]:
        a2 = AEP(C=aep.C, K=aep.K, W=aep.W, theta=aep.theta)
        attrs2 = dict(attrs)
        attrs2["device"] = self.device_tag
        return a2, attrs2

    def monotone_clock_ns(self) -> int:
        return int(self.fixed_time_ns)


def run_on_backend(aep: AEP, attrs: Dict[str, Any], be: Backend):
    set_clock_ns(lambda: be.monotone_clock_ns())
    try:
        a2, attrs2 = be.legalize(aep, attrs)
        d = launch(a2, DEFAULT_PREDICATES, attrs2)
        cd = canon_decision(d)
    finally:
        set_clock_ns(None)
    return d, cd


def run_multi_backend_and_compare(aep: AEP, attrs: Dict[str, Any], backends: List[Backend]) -> Dict[str, Any]:
    results = []
    digests = []
    for be in backends:
        d, cd = run_on_backend(aep, attrs, be)
        results.append({"backend": be.name, "decision": cd})
        digests.append(json.dumps(cd, sort_keys=True, separators=(",", ":")))
    first = digests[0]
    equal_all = all(x == first for x in digests[1:])
    return {
        "equal": bool(equal_all),
        "results": results,
    }
