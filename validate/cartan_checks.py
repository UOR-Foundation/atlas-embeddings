from __future__ import annotations

import json
import pathlib
from typing import Dict

from lie.classify import identify_dynkin
from lie.weyl_order import weyl_order_for


def collect_phase4(out_root: pathlib.Path) -> Dict[str, dict]:
    base = out_root / "artifacts" / "phase4"
    found: Dict[str, dict] = {}
    for typ in ["G2", "F4", "E6", "E7", "E8"]:
        cpath = base / typ / "cartan.json"
        if cpath.exists():
            entries = json.loads(cpath.read_text(encoding="utf-8"))
            ok_int = all(isinstance(x, int) for row in entries for x in row)
            dyn = identify_dynkin(entries)
            weyl = weyl_order_for(dyn) if dyn != "Unknown" else None
            found[typ] = {
                "integral": ok_int,
                "dynkin": dyn,
                "weyl": weyl,
            }
    return found
