#!/usr/bin/env python3
"""Check incidence signing and positive-forward, negative-reverse ordering.

The vector oracle constructs and sums actual incidence coordinates. The cut
oracle counts crossing edges directly. All simple graphs on at most five
vertices and all {-1,0,1} vertex coefficients check the energy identity.
All graphs on at most four vertices, orders, and signs check the exact folded
width formula. Cyclic ladders separate signing/folding from good layouts.
These finite checks do not establish an asymptotic improvement.
"""

from itertools import combinations, permutations, product
import json
from math import acos, pi, sqrt


def cut(edges, region):
    return sum((u in region) != (v in region) for u, v in edges)


def vector_energy(n, edges, coefficients):
    vectors = [
        [int(u == v) - int(w == v) for u, w in edges]
        for v in range(n)
    ]
    total = [sum(coefficients[v] * vectors[v][j] for v in range(n))
             for j in range(len(edges))]
    return sum(x * x for x in total)


def check_energy(n, edges, coefficients):
    region = {v for v, value in enumerate(coefficients) if value}
    discordant = sum(u in region and v in region and coefficients[u] != coefficients[v]
                     for u, v in edges)
    boundary = cut(edges, region)
    assert vector_energy(n, edges, coefficients) == boundary + 4 * discordant
    positive = {v for v in region if coefficients[v] == 1}
    negative = region - positive
    a = sum((u in positive and v not in region) or
            (v in positive and u not in region) for u, v in edges)
    b = sum((u in negative and v not in region) or
            (v in negative and u not in region) for u, v in edges)
    assert boundary == a + b
    assert cut(edges, positive) == a + discordant
    assert cut(edges, negative) == b + discordant
    assert 2 * max(cut(edges, positive), cut(edges, negative)) == (
        boundary + 2 * discordant + abs(a - b))


def width(edges, order):
    return max(cut(edges, set(order[:k])) for k in range(len(order) + 1))


def folded(order, signs):
    return [v for v in order if signs[v]] + [v for v in reversed(order) if not signs[v]]


def check_fold(edges, order, signs):
    prediction = max(
        cut(edges, {v for v in order[:k] if signs[v] == value})
        for k in range(len(order) + 1) for value in (False, True)
    )
    actual = width(edges, folded(order, signs))
    assert actual == prediction
    assert width(edges, order) <= 2 * actual


def graphs(n):
    possible = list(combinations(range(n), 2))
    for mask in range(1 << len(possible)):
        yield [edge for j, edge in enumerate(possible) if mask >> j & 1]


def ladder(m):
    edges = [(2 * i + layer, 2 * ((i + 1) % m) + layer)
             for i in range(m) for layer in (0, 1)]
    edges += [(2 * i, 2 * i + 1) for i in range(m)]
    return edges


def ladder_comparison(m):
    assert m >= 4 and m % 2 == 0
    n = 2 * m
    edges = ladder(m)
    parts = [[2 * i + layer for i in range(m) for layer in (0, 1)
              if (i + layer) % 2 == value] for value in (0, 1)]
    order = parts[0] + parts[1]
    assert all(((u // 2 + u % 2) ^ (v // 2 + v % 2)) & 1 for u, v in edges)
    cuts = [sum(((mask >> u) ^ (mask >> v)) & 1 for u, v in edges)
            for mask in range(1 << n)]
    prefixes = [0]
    for v in order:
        prefixes.append(prefixes[-1] | (1 << v))
    best = len(edges)
    best_signs = 0
    for signs in range(1 << n):
        cost = max(max(cuts[region & signs], cuts[region & ~signs]) for region in prefixes)
        if cost < best:
            best, best_signs = cost, signs
    witness = [bool(best_signs >> v & 1) for v in range(n)]
    assert width(edges, folded(order, witness)) == best
    paired = list(range(n))
    assert width(edges, paired) == 5
    initial = width(edges, order)
    assert initial == 3 * n // 2
    assert initial <= 2 * best
    return {
        "vertices": n,
        "bipartition_first_width": initial,
        "minimum_signed_peak_squared": initial,
        "minimum_width_after_one_fold": best,
        "paired_order_width": width(edges, paired),
    }


def main():
    energy_cases = fold_cases = graph_count = 0
    for n in range(6):
        for edges in graphs(n):
            graph_count += 1
            for coefficients in product((-1, 0, 1), repeat=n):
                check_energy(n, edges, coefficients)
                energy_cases += 1
            if n <= 4:
                for order in permutations(range(n)):
                    for signs in product((False, True), repeat=n):
                        check_fold(edges, order, signs)
                        fold_cases += 1
    extra_edges = [(0, 0), (0, 1), (1, 0), (1, 2), (2, 2)]
    for coefficients in product((-1, 0, 1), repeat=3):
        check_energy(3, extra_edges, coefficients)
    for order in permutations(range(3)):
        for signs in product((False, True), repeat=3):
            check_fold(extra_edges, order, signs)
    p = 3 / (2 * pi) * acos((1 + 2 * sqrt(2)) / 4)
    print(json.dumps({
        "simple_graphs_through_5_vertices": graph_count,
        "energy_cases": energy_cases,
        "fold_cases": fold_cases,
        "loop_parallel_energy_cases": 27,
        "loop_parallel_fold_cases": 48,
        "cubic_layout_p": p,
        "signing_C_needed_for_improvement": sqrt(p / 3),
        "incidence_signing_C_asymptotic_obstruction": 1 / sqrt(2),
        "cyclic_ladders": [ladder_comparison(m) for m in (4, 6, 8)],
    }, indent=2))


if __name__ == "__main__":
    main()
