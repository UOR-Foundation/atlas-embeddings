#!/usr/bin/env python3
import sys, pathlib, re

ROOT = pathlib.Path("docs")
BAN = re.compile(r"(?i)tests?\s+as\s+proofs?")
DISCLAIMER = "Computational evidence"
errors = []

for p in ROOT.rglob("*.md"):
    text = p.read_text(encoding="utf-8")
    # ban phrase globally
    if BAN.search(text):
        errors.append(f"{p}: banned phrase 'tests as proofs'")
    # require disclaimer on evidence pages
    if "docs/evidence/" in str(p).replace("\\","/"):
        if DISCLAIMER not in text:
            errors.append(f"{p}: missing evidence disclaimer block")
if errors:
    print("\n".join(errors))
    sys.exit(1)
print("docs-lint: OK")
