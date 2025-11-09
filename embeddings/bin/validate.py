#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import sys

REPO_ROOT = pathlib.Path(__file__).resolve().parents[1]
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))

from e8.roots import generate_e8_roots
from validate.cartan_checks import collect_phase4
from validate.e_specs import (
    E1_IP_MULTISET,
    E2_DEG_AVG_DEN,
    E2_DEG_AVG_NUM,
    E2_DEG_MAX,
    E2_DEG_MIN,
    E2_EDGES_PLUS1,
    EXPECTED_WEYL,
)
from validate.induced_counts import induced_subgraph_count
from validate.inner_products import multiset_counts
from validate.r96_stats import r96_stats


def _sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--iota", required=True, help="path to canonical 96-index map JSON")
    parser.add_argument(
        "--out", default="artifacts/phase7", help="output directory for validation certificates"
    )
    parser.add_argument(
        "--induced-limit",
        type=int,
        default=0,
        help="limit induced subgraph counting (0 = no limit)",
    )
    args = parser.parse_args()

    out_dir = pathlib.Path(args.out)
    out_dir.mkdir(parents=True, exist_ok=True)

    iota_path = pathlib.Path(args.iota)
    iota = json.loads(iota_path.read_text(encoding="utf-8"))

    roots = generate_e8_roots()
    vectors = [roots[k] for k in iota]

    # E1 exact inner-product multiset
    ip_counts = multiset_counts(vectors)
    e1_ok = ip_counts == E1_IP_MULTISET

    # E2 R96 graph statistics
    stats = r96_stats(iota)
    avg_num = stats["deg_avg_num"]
    avg_den = stats["deg_avg_den"]
    e2_ok = (
        stats["edges"] == E2_EDGES_PLUS1
        and stats["deg_min"] == E2_DEG_MIN
        and stats["deg_max"] == E2_DEG_MAX
        and avg_num * E2_DEG_AVG_DEN == E2_DEG_AVG_NUM * avg_den
    )

    # E3 Phase 4 Cartan verifications
    phase4 = collect_phase4(pathlib.Path("."))
    constructions = []
    e3_ok = True
    for name, info in sorted(phase4.items()):
        dyn = info["dynkin"]
        weyl_expected = EXPECTED_WEYL.get(dyn)
        ok = info["integral"] and weyl_expected is not None and info["weyl"] == weyl_expected
        constructions.append({"name": name, **info, "ok": ok})
        e3_ok = e3_ok and ok

    # Induced subgraph counting for Φ = -1 graph
    limit = args.induced_limit if args.induced_limit > 0 else None
    induced = {}
    for pattern in ("E6", "E7", "E8"):
        try:
            count = induced_subgraph_count(vectors, pattern, limit=limit)
        except Exception as exc:  # pragma: no cover - defensive diagnostic
            count = f"error:{exc}"
        induced[pattern] = count

    certificate = {
        "E1": {"counts": ip_counts, "expected": E1_IP_MULTISET, "ok": e1_ok},
        "E2": {
            "edges_plus1": stats["edges"],
            "deg_min": stats["deg_min"],
            "deg_max": stats["deg_max"],
            "deg_avg_num": avg_num,
            "deg_avg_den": avg_den,
            "expected": {
                "edges_plus1": E2_EDGES_PLUS1,
                "deg_min": E2_DEG_MIN,
                "deg_max": E2_DEG_MAX,
                "deg_avg_num": E2_DEG_AVG_NUM,
                "deg_avg_den": E2_DEG_AVG_DEN,
            },
            "cayley_free": stats["cayley_free"],
            "ok": e2_ok,
        },
        "E3": {"constructions": constructions, "ok": e3_ok},
        "induced_subgraphs_phi_minus1": induced,
    }

    certificate_text = json.dumps(certificate, sort_keys=True, separators=(",", ":"))
    digest = _sha256_text(certificate_text)

    (out_dir / "validation.json").write_text(json.dumps(certificate, indent=2), encoding="utf-8")
    (out_dir / "validation.sha256").write_text(digest + "\n", encoding="utf-8")

    print("E1", "OK" if e1_ok else "FAIL", ip_counts)
    print(
        "E2",
        "OK" if e2_ok else "FAIL",
        f"|E|={stats['edges']}",
        f"deg_min={stats['deg_min']}",
        f"deg_max={stats['deg_max']}",
        f"deg_avg={avg_num}/{avg_den}",
        f"cayley_free={stats['cayley_free']}",
    )
    if constructions:
        description = "; ".join(
            f"{item['name']}:{item['dynkin']}:{item['weyl']}:{'int' if item['integral'] else 'nonint'}"
            for item in constructions
        )
    else:
        description = "no-phase4-artifacts"
    print("E3", "OK" if e3_ok else "FAIL", description)
    print("INDUCED", json.dumps(induced, separators=(",", ":")))
    print("CERT", digest)


if __name__ == "__main__":
    main()
