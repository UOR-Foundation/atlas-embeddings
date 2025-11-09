from __future__ import annotations
from typing import List, Tuple
from .group import P_MOD

# Six anchors S = {(8m, 0): m = 0,...,5}
ANCHORS: List[Tuple[int, int]] = [((8 * m) % P_MOD, 0) for m in range(6)]
