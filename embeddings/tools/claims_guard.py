#!/usr/bin/env python3
import sys, pathlib, re

ROOT = pathlib.Path(".")
FILES = [p for ext in (".md", ".tex") for p in ROOT.rglob(f"*{ext}")]

# bans
BAN_PATTERNS = [
    re.compile(r"(?i)\bno\s+sixth\s+exceptional\s+group\b"),
    re.compile(r"(?i)\btests?\s+as\s+proofs?\b"),
]

# required labeling rules
RULES = [
    # any "initiality" must be in a conjectural context
    dict(name="initiality-labeled-conjecture",
         pat=re.compile(r"(?i)\binitiality\b"),
         must_near=re.compile(r"(?i)\bconjectur"),
         window=3),
    # any "exceptional constructions" must be conjecture or explicitly "evidence"
    dict(name="exceptional-labeled",
         pat=re.compile(r"(?i)\bexceptional\s+constructions?\b"),
         must_near=re.compile(r"(?i)\bconjectur|evidence\b"),
         window=3),
    # embedding must be named as theorem in proofs
    dict(name="embedding-theorem-in-proofs",
         file_include="docs/proofs/atlas_to_e8_embedding.md",
         must_contain=re.compile(r"(?i)\btheorem\b.*atlas.*e8|atlas.*e8.*\btheorem\b")),
]

errors=[]

for p in FILES:
    text = p.read_text(encoding="utf-8", errors="ignore").splitlines()

    # bans
    for i, line in enumerate(text, 1):
        for rx in BAN_PATTERNS:
            if rx.search(line):
                errors.append(f"{p}:{i}: banned claim")

    # rules
    for i, line in enumerate(text, 1):
        for r in RULES:
            if "file_include" in r and r["file_include"] != str(p).replace("\\","/"):
                continue
            if "must_contain" in r:
                if not r["must_contain"].search("\n".join(text)):
                    errors.append(f"{p}: missing required marker for {r['name']}")
                continue
            if r["pat"].search(line):
                lo=max(1, i-r["window"]); hi=min(len(text), i+r["window"])
                window_text="\n".join(text[lo-1:hi])
                if not r["must_near"].search(window_text):
                    errors.append(f"{p}:{i}: unlabeled occurrence violates {r['name']}")

# evidence pages must contain the disclaimer block
for p in ROOT.rglob("docs/evidence/*.md"):
    s = p.read_text(encoding="utf-8", errors="ignore")
    if "Computational evidence" not in s:
        errors.append(f"{p}: missing evidence disclaimer")

if errors:
    print("\n".join(errors)); sys.exit(1)
print("claims-guard: OK")
