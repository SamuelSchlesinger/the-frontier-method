#!/usr/bin/env python3
"""Validates: optimal cut partitions can be incompatible, and union quotients
can double accepting-path counts while representative quotients preserve them.

This exhausts the transition relations between the two prescribed cuts and
independently enumerates every word/path of the explicit three-bit automata.
It is a finite check of the examples in ../index.md, not an asymptotic theorem.
"""

from itertools import combinations, product


def boolean_product(left, right):
    return [[int(any(a and b for a, b in zip(row, col)))
             for col in zip(*right)] for row in left]


def rectangle_cover_number(matrix):
    nr, nc = len(matrix), len(matrix[0])
    support = {(i, j) for i in range(nr) for j in range(nc) if matrix[i][j]}
    rectangles = []
    for rows in range(1, 1 << nr):
        for cols in range(1, 1 << nc):
            rectangle = {(i, j) for i in range(nr) for j in range(nc)
                         if (rows >> i) & 1 and (cols >> j) & 1}
            if rectangle <= support:
                rectangles.append(rectangle)
    for count in range(1, len(support) + 1):
        if any(set().union(*cover) == support
               for cover in combinations(rectangles, count)):
            return count
    return 0


language = {"000", "100", "101"}
u1, v1 = [[1, 0], [1, 1]], [[1, 0, 0, 0], [0, 1, 0, 0]]
u2, v2 = [[1, 0], [0, 0], [0, 1], [0, 0]], [[1, 0], [1, 1]]
m1 = [[int(str(p) + format(z, "02b") in language) for z in range(4)]
      for p in range(2)]
m2 = [[int(format(p, "02b") + str(z) in language) for z in range(2)]
      for p in range(4)]
assert boolean_product(u1, v1) == m1
assert boolean_product(u2, v2) == m2
assert rectangle_cover_number(m1) == rectangle_cover_number(m2) == 2
compatible = 0
for bits in product((0, 1), repeat=8):
    edge = lambda a, r, q: bits[4 * a + 2 * r + q]
    prefix_ok = all(u2[2 * p + a][q] == int(any(
        u1[p][r] and edge(a, r, q) for r in range(2)))
        for p, a, q in product(range(2), repeat=3))
    suffix_ok = all(v1[r][2 * a + b] == int(any(
        edge(a, r, q) and v2[q][b] for q in range(2)))
        for r, a, b in product(range(2), repeat=3))
    compatible += prefix_ok and suffix_ok
assert compatible == 0
print("Both prescribed cut partitions are optimal (2 rectangles each).")
print("Compatible transition relations: 0 of 256.")

# Edges are triples (source, bit, destination); all states have fixed layers.
edges = {
    ("s", "0", "p"), ("s", "1", "q"),
    ("p", "0", "r"), ("q", "0", "r0"), ("q", "0", "r1"),
    ("r", "0", "t"), ("r", "1", "t"),
    ("r0", "0", "t"), ("r1", "1", "t"),
}


def paths(graph, state, word):
    if not word:
        return int(state == "t")
    return sum(paths(graph, target, word[1:])
               for source, bit, target in graph
               if source == state and bit == word[0])


words = ["".join(bits) for bits in product("01", repeat=3)]
suffixes = ["".join(bits) for bits in product("01", repeat=2)]
assert [paths(edges, "p", w) for w in suffixes] == [1, 1, 0, 0]
assert [paths(edges, "q", w) for w in suffixes] == [1, 1, 0, 0]
quotient = lambda state: "pq" if state in {"p", "q"} else state
union_edges = {(quotient(s), a, quotient(t)) for s, a, t in edges}
representative_edges = {(quotient(s), a, quotient(t)) for s, a, t in edges
                        if s != "q"}
original_counts = [paths(edges, "s", w) for w in words]
union_counts = [paths(union_edges, "s", w) for w in words]
representative_counts = [paths(representative_edges, "s", w) for w in words]
assert original_counts == [1, 1, 0, 0, 1, 1, 0, 0]
assert union_counts == [2 * count for count in original_counts]
assert representative_counts == original_counts
assert [bool(c) for c in original_counts] == [bool(c) for c in union_counts]
print("Accepted words: 4 in the original, union, and representative graphs.")
print("Accepting paths: original 4; union quotient 8; representative quotient 4.")
