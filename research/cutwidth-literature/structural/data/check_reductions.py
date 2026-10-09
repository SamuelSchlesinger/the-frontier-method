#!/usr/bin/env python3
"""Validates: triangle lifting costs <=1; its density and deletion budgets.

The local check exhausts all port-side patterns. Global checks compare independently
counted frontiers before/after lifting every order and expansion subset of K4/K3,3.
This validates the finite cases, not a replacement for the paper proof.
"""

from itertools import combinations, permutations, product
from math import acos, pi, sqrt


def width(edges, order):
    position = {v: i for i, v in enumerate(order)}
    return max(
        (sum((position[u] < k) != (position[v] < k) for u, v in edges)
         for k in range(len(order) + 1)), default=0)


def expand_and_lift(edges, order, expanded):
    position = {v: i for i, v in enumerate(order)}
    incident = {v: [] for v in order}
    for e, (u, v) in enumerate(edges):
        incident[u].append((e, v))
        incident[v].append((e, u))
    lifted = []
    new_edges = []
    for v in order:
        if v in expanded:
            ports = [(v, e) for e, w in sorted(
                incident[v], key=lambda ew: (position[ew[1]], ew[0]))]
            assert len(ports) == 3
            lifted.extend(ports)
            new_edges.extend(combinations(ports, 2))
        else:
            lifted.append((v, -1))
    for e, (u, v) in enumerate(edges):
        new_edges.append(((u, e if u in expanded else -1),
                          (v, e if v in expanded else -1)))
    return new_edges, lifted


def main():
    local = 0
    for sides in product((0, 1), repeat=3):  # 1 means earlier external endpoint
        order = sorted(range(3), key=lambda v: -sides[v])
        a = sum(sides)
        for j in (1, 2):
            prefix = set(order[:j])
            actual = 2 + sum((v in prefix) != bool(sides[v]) for v in range(3))
            assert actual == 2 + abs(a-j)
            assert actual <= max(a, 3-a) + 1
            local += 1
    print(f"Triangle local patterns: {local} checks passed")
    cases = [
        ("K4", list(range(4)), list(combinations(range(4), 2))),
        ("K3,3", list(range(6)), [(u, v) for u in range(3) for v in range(3, 6)]),
        ("three parallel edges", [0, 1], [(0, 1)] * 3),
    ]
    for name, vertices, edges in cases:
        checks = 0
        for order in permutations(vertices):
            old = width(edges, order)
            for bits in product((0, 1), repeat=len(vertices)):
                expanded = {v for v, bit in zip(vertices, bits) if bit}
                new_edges, lifted = expand_and_lift(edges, order, expanded)
                assert width(new_edges, lifted) <= old + bool(expanded)
                checks += 1
        print(f"{name}: {checks} global lifts passed")
    p = 3 * acos((1 + 2 * sqrt(2))/4) / (2*pi)
    for target in (4.6, 5.0):
        c = 1 / (2 * (target-1))
        fraction = 1.5 * (1-c/p)
        print(f"L={target:.1f}: triangle vertex fraction >= {fraction:.12f}")
    c = 0.138781
    print(f"Illustrative deletion fraction < {(p-c)/(3-c):.12f}")


if __name__ == "__main__":
    main()
