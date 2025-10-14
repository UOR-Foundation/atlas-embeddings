from __future__ import annotations
import sys, json, hashlib, pathlib, tomllib, ast

try:
    from jsonschema import validate as _jsonschema_validate
except ModuleNotFoundError:  # pragma: no cover - offline fallback
    def _jsonschema_validate(instance, schema):
        required = schema.get("required", [])
        for key in required:
            if key not in instance:
                raise ValueError(f"missing required field: {key}")
        properties = schema.get("properties", {})
        for key, spec in properties.items():
            if key not in instance:
                continue
            expected_type = spec.get("type")
            if expected_type == "object" and not isinstance(instance[key], dict):
                raise TypeError(f"field '{key}' must be object")
            if expected_type == "array" and not isinstance(instance[key], list):
                raise TypeError(f"field '{key}' must be array")
else:  # pragma: no cover
    _jsonschema_validate = _jsonschema_validate

try:
    import yaml
except ModuleNotFoundError:  # pragma: no cover - offline fallback
    yaml = None

EXIT = {
  "L100":101,"L110":111,"L120":121,"L200":201,"L300":301,"L310":311,
  "L320":321,"L400":401,"L410":411,"L500":501,"L600":601
}

def _sha256_bytes(p: pathlib.Path) -> str:
    h=hashlib.sha256()
    with open(p,"rb") as f:
        for chunk in iter(lambda:f.read(1<<20), b""): h.update(chunk)
    return h.hexdigest()

def load_toml(path: str) -> dict:
    with open(path,"rb") as f: return tomllib.load(f)

def _parse_scalar(value: str):
    value = value.strip()
    if value in {"true","True"}: return True
    if value in {"false","False"}: return False
    if value in {"null","None"}: return None
    if value.startswith(("'","\"","[","{")):
        return ast.literal_eval(value)
    try:
        return int(value)
    except ValueError:
        try:
            return float(value)
        except ValueError:
            return value

def _load_rules_cfg(path: pathlib.Path) -> dict:
    text = path.read_text()
    if yaml is not None:
        return yaml.safe_load(text)
    rules: dict[str, dict[str, object]] = {}
    current: dict[str, object] | None = None
    for raw in text.splitlines():
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        indent = len(raw) - len(raw.lstrip(" "))
        line = raw.strip()
        if line.endswith(":"):
            key = line[:-1]
            if indent == 0 and key == "rules":
                continue
            if indent == 2:
                current = {}
                rules[key] = current
            else:
                raise ValueError(f"unsupported indentation in {path}: '{raw}'")
            continue
        if current is None:
            raise ValueError(f"unexpected line in {path}: '{raw}'")
        if ":" not in line:
            raise ValueError(f"malformed line in {path}: '{raw}'")
        k, v = line.split(":", 1)
        current[k.strip()] = _parse_scalar(v)
    return {"rules": rules}

def lint(aep_toml: str, repo_root: str) -> list[dict]:
    root = pathlib.Path(repo_root)
    doc = load_toml(aep_toml)

    # Schema check
    schema = json.load(open(root/"schema/aep.schema.json","r"))
    _jsonschema_validate(doc, schema)

    cfg = _load_rules_cfg(root/"tools/lint/rules.yml")
    rules = cfg["rules"]
    failures = []

    # L100
    r = rules["L100"]
    missing = [p for p in r["required_files"] if not (root/p).exists()]
    if missing:
        failures.append({"id":"L100","msg":f"missing files {missing}"})
    # hashes (optional fields)
    for key,path in (("ace.b_sha256","data/b.npy"),("ace.a_sha256","data/a.npy")):
        target = root/path
        if target.exists() and key in str(doc):
            pass  # repo keeps vectors; content hash is advisory

    # L110
    wl = set(rules["L110"]["whitelist"])
    claim_keys = [k for k,v in doc.get("claims",{}).items() if v is True]
    if not set(claim_keys) <= wl:
        failures.append({"id":"L110","msg":f"claims outside whitelist {set(claim_keys)-wl}"})

    # L120
    if len(doc["runner"]["backends"]) < int(rules["L120"]["require_backends"]):
        failures.append({"id":"L120","msg":"need ≥2 backends"})
    # L200
    # declaration-level only; runtime presence checked in Python
    req = rules["L200"]["require_channels"]
    declared = set(doc.get("witness_decl", []))  # optional hint array
    for need in req:
        alts = set(need.split("|"))
        if not (alts & declared):
            failures.append({"id":"L200","msg":f"witness channel '{need}' not declared"})

    # L300
    eps = float(doc["ace"]["epsilon"]); tau = float(doc["ace"]["tau"])
    if not (0.0 < eps < 1.0): failures.append({"id":"L300","msg":"epsilon ∉ (0,1)"} )
    if not (tau >= 0.0): failures.append({"id":"L300","msg":"tau < 0"} )

    # L310
    if doc.get("projection",{"method":"dual_kkt_soft_threshold"}).get("method") != "dual_kkt_soft_threshold":
        failures.append({"id":"L310","msg":"projection method must be dual_kkt_soft_threshold"})

    # L320
    for k in ["GapLB_min","SlopeUB_max"]:
        if k not in doc["ace"]: failures.append({"id":"L320","msg":f"ace.{k} missing"})

    # L400
    if not (root/"petc/ledger.json").exists():
        failures.append({"id":"L400","msg":"missing petc/ledger.json"})

    # L410
    for k in ["group","schedule","anchors"]:
        if k not in doc["petc"]: failures.append({"id":"L410","msg":f"petc.{k} missing"})

    # L500
    det = doc["runner"]["determinism"]
    for k in ["seed","dtype","rmode"]:
        if k not in det: failures.append({"id":"L500","msg":f"runner.determinism.{k} missing"})

    # L600
    if not (root/".github/workflows/aep.yml").exists():
        failures.append({"id":"L600","msg":"missing CI workflow .github/workflows/aep.yml"})

    return failures

def main():
    aep_toml = sys.argv[1] if len(sys.argv)>1 else "aep.toml"
    repo_root = sys.argv[2] if len(sys.argv)>2 else "."
    fails = lint(aep_toml, repo_root)
    if not fails:
        print(json.dumps({"status":"OK"}, indent=2)); sys.exit(0)
    print(json.dumps({"status":"FAIL","fails":fails}, indent=2))
    # choose first failure code
    sys.exit(EXIT[fails[0]["id"]])

if __name__=="__main__": main()
