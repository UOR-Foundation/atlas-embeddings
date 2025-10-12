from __future__ import annotations

import json
import pathlib
import zipfile
from typing import Any, Dict, Iterable, Iterator, List, MutableMapping, Sequence


int8 = int
int64 = int


class ndarray(List[int]):
    def __init__(self, data: Iterable[Any], dtype: Any | None = None):
        super().__init__(data)
        self.dtype = dtype

    def tolist(self) -> List[Any]:  # pragma: no cover - compatibility helper
        return list(self)


def array(data: Iterable[Any], dtype: Any | None = None) -> ndarray:
    if isinstance(data, ndarray):
        seq = list(data)
    else:
        seq = list(data)
    if dtype is not None:
        seq = [dtype(x) for x in seq]
    return ndarray(seq, dtype=dtype)


def array_equal(a: Sequence[Any], b: Sequence[Any]) -> bool:
    return list(a) == list(b)


class _NpzFile:
    def __init__(self, mapping: MutableMapping[str, Any]):
        self._mapping = mapping

    def __getitem__(self, key: str) -> Any:
        item = self._mapping[key]
        kind = item.get("kind")
        if kind == "array":
            return array(item["data"])
        return item["data"]

    def keys(self) -> Iterator[str]:
        return iter(self._mapping.keys())


def savez_compressed(file: str | pathlib.Path, **arrays: Any) -> None:
    path = pathlib.Path(file)
    serial: Dict[str, Dict[str, Any]] = {}
    for key, value in arrays.items():
        if isinstance(value, ndarray):
            serial[key] = {"kind": "array", "data": list(value)}
        elif isinstance(value, (list, tuple)):
            serial[key] = {"kind": "array", "data": list(value)}
        else:
            serial[key] = {"kind": "scalar", "data": value}

    payload = json.dumps(serial).encode("utf-8")
    with zipfile.ZipFile(path, "w", compression=zipfile.ZIP_DEFLATED) as zf:
        zf.writestr("data.json", payload)


def load(file: str | pathlib.Path) -> _NpzFile:
    path = pathlib.Path(file)
    with zipfile.ZipFile(path, "r") as zf:
        data = json.loads(zf.read("data.json").decode("utf-8"))
    return _NpzFile(data)
