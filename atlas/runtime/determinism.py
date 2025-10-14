from __future__ import annotations
from dataclasses import dataclass
from typing import Dict, Any, List
import json
import hashlib

from atlas.aep.decision_rules import canon_decision


@dataclass(frozen=True)
class EvidenceVector:
    status: str
    code: int
    reason: str
    evidence: Dict[str, Any]
    log: List[Dict[str, Any]]


def evidence_vector(decision_obj) -> EvidenceVector:
    cd = canon_decision(decision_obj)
    return EvidenceVector(
        status=cd["status"],
        code=int(cd["code"]),
        reason=cd["reason"],
        evidence=cd["evidence"],
        log=cd["log"],
    )


def evidence_digest(ev: EvidenceVector) -> str:
    payload = {
        "status": ev.status,
        "code": ev.code,
        "reason": ev.reason,
        "evidence": ev.evidence,
        "log": ev.log,
    }
    j = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(j.encode("utf-8")).hexdigest()


def equal_evidence(a: EvidenceVector, b: EvidenceVector) -> bool:
    return evidence_digest(a) == evidence_digest(b)
