#!/usr/bin/env python3
"""Independent finite checks of mixed-fiber ranks and terminal pathwidth.

Gaussian elimination computes ranks; enumerated input/output observations compute
fiber sizes. These examples do not prove an asymptotic lower bound.
"""

from collections import Counter
from itertools import permutations, product


def rank(rows, q):
    basis = {}
    for row in rows:
        row = list(row)
        for pivot, vector in sorted(basis.items()):
            factor = row[pivot]
            row = [(a - factor * b) % q for a, b in zip(row, vector)]
        pivot = next((i for i, a in enumerate(row) if a), None)
        if pivot is not None:
            scale = pow(row[pivot], -1, q)
            basis[pivot] = [(a * scale) % q for a in row]
    return len(basis)


def systematic(matrix):
    n = len(matrix[0])
    return [tuple(int(i == j) for j in range(n)) for i in range(n)] + list(matrix)


def connectivity(rows, subset, q):
    n = len(rows[0])
    return (rank([row for i, row in enumerate(rows) if i in subset], q)
            + rank([row for i, row in enumerate(rows) if i not in subset], q) - n)


def check_fibers(matrix, q):
    rows = systematic(matrix)
    n = len(matrix[0])
    words = list(product(range(q), repeat=n))
    code = [tuple(sum(a * b for a, b in zip(row, x)) % q for row in rows)
            for x in words]
    for mask in range(1 << len(rows)):
        subset = {i for i in range(len(rows)) if mask & (1 << i)}
        left_rank = rank([row for i, row in enumerate(rows) if i in subset], q)
        right_rank = rank([row for i, row in enumerate(rows) if i not in subset], q)
        left = Counter(tuple(word[i] for i in sorted(subset)) for word in code)
        right = Counter(tuple(word[i] for i in range(len(rows)) if i not in subset)
                        for word in code)
        assert set(left.values()) == {q ** (n - left_rank)}
        assert set(right.values()) == {q ** (n - right_rank)}
        lam = connectivity(rows, subset, q)
        assert lam >= 0
        assert q ** lam * max(left.values()) * max(right.values()) == q ** n
    return 1 << len(rows)


def pathwidth(matrix, q):
    rows = systematic(matrix)
    return min(max(connectivity(rows, set(order[:t]), q) for t in range(len(rows) + 1))
               for order in permutations(range(len(rows))))


def main():
    checked = 0
    for n in range(1, 4):
        for entries in product(range(2), repeat=n * n):
            matrix = [entries[i * n:(i + 1) * n] for i in range(n)]
            checked += check_fibers(matrix, 2)
    # Direct sums have maximum pathwidth, not the sum of the block pathwidths.
    assert pathwidth([(1,)], 2) == 1
    assert pathwidth([(1, 0), (0, 1)], 2) == 1
    assert pathwidth([(0, 0), (0, 0)], 2) == 0
    mds = [(1, 1), (1, 2)]
    checked += check_fibers(mds, 3)
    assert pathwidth(mds, 3) == 2
    print(f"Rank profiles: {checked} matrix/cut pairs matched enumerated fiber sizes; "
          "identity, zero, direct-sum, and ternary MDS pathwidth controls passed.")


if __name__ == "__main__":
    main()
