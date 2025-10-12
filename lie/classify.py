from __future__ import annotations

from typing import List


def _is_simply_laced(A: List[List[int]]) -> bool:
    n = len(A)
    for i in range(n):
        for j in range(n):
            if i == j:
                if A[i][j] != 2:
                    return False
            else:
                if A[i][j] not in (0, -1):
                    return False
    return True


def _degree_multiset(A: List[List[int]]) -> List[int]:
    n = len(A)
    degrees: List[int] = []
    for i in range(n):
        d = sum(1 for j in range(n) if j != i and A[i][j] == -1 and A[j][i] == -1)
        degrees.append(d)
    return sorted(degrees)


def identify_dynkin(A: List[List[int]]) -> str:
    n = len(A)
    if n in (6, 7, 8) and _is_simply_laced(A):
        deg = _degree_multiset(A)
        if n == 6 and deg == [1, 1, 1, 2, 2, 3]:
            return "E6"
        if n == 7 and deg == [1, 1, 1, 2, 2, 2, 3]:
            return "E7"
        if n == 8 and deg == [1, 1, 1, 2, 2, 2, 2, 3]:
            return "E8"
    if n == 2:
        prod = abs(A[0][1] * A[1][0])
        if prod == 3:
            return "G2"
    if n == 4:
        asym = [
            (i, j)
            for i in range(4)
            for j in range(4)
            if i != j and (A[i][j], A[j][i]) in {(-1, -2), (-2, -1)}
        ]
        if len(asym) == 2:
            return "F4"
    return "Unknown"
