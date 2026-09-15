#!/usr/bin/env python3
"""Independent standard-library verifier for the q=5, K_21 certificate."""

from __future__ import annotations

from collections import Counter
from hashlib import sha256
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
MATRIX_PATH = HERE / "q5_k21_matrix.txt"
N = 21
COLOURS = set(range(10))


def load_matrix(path: Path) -> list[list[int | None]]:
    rows = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        rows.append([None if token == "." else int(token) for token in line.split()])
    return rows


def main() -> None:
    matrix = load_matrix(MATRIX_PATH)
    assert len(matrix) == N
    assert all(len(row) == N for row in matrix)
    assert all(matrix[v][v] is None for v in range(N))
    assert all(matrix[v][w] == matrix[w][v] for v in range(N) for w in range(N))
    assert all(matrix[v][w] in COLOURS for v in range(N) for w in range(N) if v != w)

    for v in range(N):
        degrees = Counter(matrix[v][w] for w in range(N) if w != v)
        assert degrees == Counter({colour: 2 for colour in COLOURS})

    edge_counts = Counter(matrix[v][w] for v in range(N) for w in range(v + 1, N))
    assert edge_counts == Counter({colour: 21 for colour in COLOURS})

    checked = 0
    for vertices in combinations(range(N), 5):
        edge_colours = [matrix[v][w] for v, w in combinations(vertices, 2)]
        assert len(set(edge_colours)) < 10, f"rainbow K5 at {vertices}"
        checked += 1
    assert checked == 20_349

    digest = sha256(MATRIX_PATH.read_bytes()).hexdigest()
    print("q=5 certificate verified")
    print(f"vertices={N} colours={len(COLOURS)} degree_per_colour=2")
    print(f"edges_per_colour=21 checked_K5={checked} rainbow_K5=0")
    print(f"sha256={digest}")


if __name__ == "__main__":
    main()
