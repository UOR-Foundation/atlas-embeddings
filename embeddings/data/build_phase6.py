from __future__ import annotations

import json
import pathlib
import hashlib
from collections import Counter
from typing import Iterable, List, Sequence, Tuple

import numpy as np
from fractions import Fraction as Q

from tools.fracfmt import qstr
from e8.roots import generate_e8_roots, dot
from r96.build import build_r96
from lie.classify import identify_dynkin

ROOT = pathlib.Path(".").resolve()
OUT = ROOT / "artifacts" / "phase6"


def write_text(path: pathlib.Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def write_lines(path: pathlib.Path, lines: Iterable[str]) -> None:
    seq = list(lines)
    text = "\n".join(seq)
    if seq:
        text += "\n"
    write_text(path, text)


def sha256_file(path: pathlib.Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def coordinates_96(iota: Sequence[int]) -> List[Tuple[Q, ...]]:
    roots = generate_e8_roots()
    return [roots[k] for k in iota]


def write_vectors_csv(path: pathlib.Path, vecs: Sequence[Tuple[Q, ...]]) -> None:
    lines: List[str] = []
    for idx, vec in enumerate(vecs):
        fields = [str(idx)] + [qstr(component) for component in vec]
        lines.append(",".join(fields))
    write_lines(path, lines)


def all_pairs_inner_products(vecs: Sequence[Tuple[Q, ...]]) -> List[str]:
    lines: List[str] = []
    for i in range(len(vecs)):
        for j in range(i + 1, len(vecs)):
            ip = dot(vecs[i], vecs[j])
            lines.append(f"{i},{j},{qstr(ip)}")
    return lines


def edge_nonedge_splits_plus1(vecs: Sequence[Tuple[Q, ...]]) -> Tuple[List[str], List[str]]:
    edges: List[str] = []
    nonedges: List[str] = []
    for i in range(len(vecs)):
        for j in range(i + 1, len(vecs)):
            ip = dot(vecs[i], vecs[j])
            if ip == Q(1):
                edges.append(f"{i},{j}")
            else:
                nonedges.append(f"{i},{j}")
    return edges, nonedges


def degree_distribution_json(degrees: Sequence[int]) -> str:
    histogram = Counter(degrees)
    avg = Q(sum(degrees), len(degrees)) if degrees else Q(0)
    payload = {
        "n": len(degrees),
        "edges": sum(degrees) // 2,
        "degree_min": min(degrees) if degrees else 0,
        "degree_max": max(degrees) if degrees else 0,
        "degree_avg": {"numerator": avg.numerator, "denominator": avg.denominator},
        "histogram": [
            {"degree": degree, "count": histogram[degree]}
            for degree in sorted(histogram)
        ],
    }
    return json.dumps(payload, indent=2, ensure_ascii=False)


def save_csr_npz(path: pathlib.Path, csr) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    np.savez_compressed(
        path,
        n=csr.n,
        indptr=np.array(csr.indptr, dtype=np.int64),
        indices=np.array(csr.indices, dtype=np.int64),
        data=np.array(csr.data, dtype=np.int8),
    )


def copy_phase4_cartans(outdir: pathlib.Path) -> List[pathlib.Path]:
    written: List[pathlib.Path] = []
    for typ in ["G2", "F4", "E6", "E7", "E8"]:
        src = ROOT / "artifacts" / "phase4" / typ / "cartan.json"
        if not src.exists():
            continue
        dst_dir = outdir / "cartans" / typ
        dst_dir.mkdir(parents=True, exist_ok=True)
        dst = dst_dir / "cartan.json"
        dst.write_bytes(src.read_bytes())
        written.append(dst)

        cartan_matrix = json.loads(src.read_text(encoding="utf-8"))
        dynkin = identify_dynkin(cartan_matrix)
        dynkin_path = dst_dir / "dynkin_type.txt"
        dynkin_path.write_text(dynkin + "\n", encoding="utf-8")
        written.append(dynkin_path)
    return written


def _clean_directory(path: pathlib.Path) -> None:
    if not path.exists():
        return
    for child in sorted(path.rglob("*"), key=lambda p: (p.is_file(), p.as_posix()), reverse=True):
        if child.is_file():
            child.unlink()
        else:
            child.rmdir()


def build(iota_path: str, out_dir: str) -> None:
    out = pathlib.Path(out_dir)
    _clean_directory(out)
    out.mkdir(parents=True, exist_ok=True)

    iota = json.loads(pathlib.Path(iota_path).read_text(encoding="utf-8"))
    write_text(out / "iota.json", json.dumps(iota, separators=(",", ":")))

    vectors = coordinates_96(iota)
    write_vectors_csv(out / "vectors96.csv", vectors)

    write_lines(out / "inner_products_upper.csv", all_pairs_inner_products(vectors))

    edges, nonedges = edge_nonedge_splits_plus1(vectors)
    write_lines(out / "edges_plus1.csv", edges)
    write_lines(out / "nonedges_plus1.csv", nonedges)

    graph = build_r96(iota=iota, closure_negation=False)
    save_csr_npz(out / "r96_csr.npz", graph.csr)
    write_text(out / "degree_stats.json", degree_distribution_json(graph.degrees))

    cartan_paths = copy_phase4_cartans(out)

    manifest_paths = [
        out / "iota.json",
        out / "vectors96.csv",
        out / "inner_products_upper.csv",
        out / "edges_plus1.csv",
        out / "nonedges_plus1.csv",
        out / "r96_csr.npz",
        out / "degree_stats.json",
    ] + cartan_paths

    records = []
    for path in sorted(manifest_paths, key=lambda p: p.relative_to(out).as_posix()):
        relative = path.relative_to(out).as_posix()
        records.append({
            "path": relative,
            "sha256": sha256_file(path),
        })

    write_text(out / "manifest.json", json.dumps({"files": records}, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser()
    parser.add_argument("--iota", required=True, help="path to canonical 96-index map JSON")
    parser.add_argument("--out", default=str(OUT), help="output directory (will be cleaned)")
    args = parser.parse_args()
    build(args.iota, args.out)
