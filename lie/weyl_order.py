from __future__ import annotations

WEYL_ORDER = {
    "G2": 12,
    "F4": 1152,
    "E6": 51840,
    "E7": 2903040,
    "E8": 696729600,
}


def weyl_order_for(type_name: str) -> int:
    if type_name not in WEYL_ORDER:
        raise ValueError(f"unknown type {type_name}")
    return WEYL_ORDER[type_name]
