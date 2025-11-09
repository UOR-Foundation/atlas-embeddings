#!/usr/bin/env python3
import json, re, sys, pathlib, fnmatch

cfg = json.load(open("docs/terminology.json"))
root = pathlib.Path(".")

def want(path):
    p = str(path)
    return any(fnmatch.fnmatch(p, pat) for pat in cfg["include"]) and not any(
        fnmatch.fnmatch(p, pat) for pat in cfg["exclude"]
    )

rules = [(r["name"], re.compile(r["pattern"]), r["replacement"]) for r in cfg["rules"]]

changed = 0
for path in (p for p in root.rglob("*") if p.is_file() and want(p)):
    try:
        text = path.read_text(encoding="utf-8")
    except Exception:
        continue
    orig = text
    for _, rx, repl in rules:
        text = rx.sub(repl, text)
    if text != orig:
        path.write_text(text, encoding="utf-8")
        print(f"fixed: {path}")
        changed += 1

print(f"files_changed={changed}")
sys.exit(0)
