#!/usr/bin/env python3
import json, re, sys, pathlib, fnmatch

cfg = json.load(open("docs/terminology.json"))
root = pathlib.Path(".")

def want(path):
    p = str(path)
    return any(fnmatch.fnmatch(p, pat) for pat in cfg["include"]) and not any(
        fnmatch.fnmatch(p, pat) for pat in cfg["exclude"]
    )

rules = [(r["name"], re.compile(r["pattern"])) for r in cfg["rules"]]
errors = []

for path in (p for p in root.rglob("*") if p.is_file() and want(p)):
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except Exception:
        continue
    for i, line in enumerate(lines, 1):
        for name, rx in rules:
            for m in rx.finditer(line):
                span = m.group(0)
                errors.append(f"{path}:{i}: {name}: banned phrase: {span!r}")

if errors:
    print("\n".join(errors))
    sys.exit(1)
print("terminology: OK")
