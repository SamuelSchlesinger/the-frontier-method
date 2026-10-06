#!/usr/bin/env python3
"""Validates: finite join budgets equal line-graph treewidth plus one.

Independent subset recurrences compute region joins, linear transitions, and
filled-neighbour elimination in the line graph. These finite tests do not prove
an asymptotic layout coefficient. Python standard library only.
"""

from itertools import combinations
import json


def boundary_masks(n, edges):
    cuts = []
    for region in range(1 << n):
        mask = 0
        for i, (u, v) in enumerate(edges):
            if ((region >> u) ^ (region >> v)) & 1:
                mask |= 1 << i
        cuts.append(mask)
    return cuts


def region_widths(n, edges):
    """Optimize actual joins and adjacent-boundary unions, not single cuts."""
    cuts = boundary_masks(n, edges)
    size = 1 << n
    infinity = len(edges) + 1
    joins = [infinity] * size
    linear = [infinity] * size
    cutwidth = [infinity] * size
    joins[0] = linear[0] = cutwidth[0] = 0
    for region in range(1, size):
        anchor = region & -region
        if region == anchor:
            joins[region] = cuts[region].bit_count()
        else:
            left = (region - 1) & region
            while left:
                if left & anchor:
                    right = region ^ left
                    cost = (cuts[left] | cuts[right]).bit_count()
                    joins[region] = min(
                        joins[region], max(joins[left], joins[right], cost)
                    )
                left = (left - 1) & region
        bits = region
        while bits:
            vertex = bits & -bits
            before = region ^ vertex
            cost = (cuts[before] | cuts[region]).bit_count()
            linear[region] = min(linear[region], max(linear[before], cost))
            cutwidth[region] = min(
                cutwidth[region], max(cutwidth[before], cuts[region].bit_count())
            )
            bits ^= vertex
    return joins[-1], linear[-1], cutwidth[-1]


def line_graph_treewidth(edges):
    """Exact elimination DP; filled edges are reconstructed from removed sets."""
    m = len(edges)
    if m == 0:
        return -1
    adjacent = [0] * m
    for i, a in enumerate(edges):
        for j, b in enumerate(edges):
            if i != j and set(a) & set(b):
                adjacent[i] |= 1 << j
    full = (1 << m) - 1
    widths = [m] * (1 << m)
    widths[0] = 0
    for removed in range(1 << m):
        remaining = full ^ removed
        bits = remaining
        while bits:
            bit = bits & -bits
            v = bit.bit_length() - 1
            reached = adjacent[v]
            todo = reached & removed
            visited = 0
            while todo:
                next_bit = todo & -todo
                todo ^= next_bit
                if next_bit & visited:
                    continue
                visited |= next_bit
                reached |= adjacent[next_bit.bit_length() - 1]
                todo |= reached & removed & ~visited
            degree = (reached & remaining & ~bit).bit_count()
            after = removed | bit
            widths[after] = min(widths[after], max(widths[removed], degree))
            bits ^= bit
    return widths[-1]


def components(n, edges):
    parent = list(range(n))

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    for u, v in edges:
        parent[find(u)] = find(v)
    return len({find(v) for v in range(n)})


def check(n, edges):
    edges = sorted({tuple(sorted(edge)) for edge in edges})
    join, linear, cut = region_widths(n, edges)
    treewidth = line_graph_treewidth(edges)
    assert join == treewidth + 1, (n, edges, join, treewidth)
    assert join <= linear
    assert cut <= linear <= cut + max(
        [sum(v in edge for edge in edges) for v in range(n)], default=0
    )
    return {
        "vertices": n,
        "edges": len(edges),
        "cycle_rank": len(edges) - n + components(n, edges),
        "cutwidth": cut,
        "linear_transition": linear,
        "join": join,
        "line_graph_treewidth": treewidth,
    }


def main():
    count = 0
    strict = 0
    for n in range(1, 6):
        possible = list(combinations(range(n), 2))
        for mask in range(1 << len(possible)):
            edges = [edge for j, edge in enumerate(possible) if mask >> j & 1]
            result = check(n, edges)
            count += 1
            strict += result["join"] < result["linear_transition"]
    samples = {
        "binary_tree_7": (7, [(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6)]),
        "three_branches_10": (10, [(0, i) for i in range(1, 4)]
            + [(i, 2 * i + 2) for i in range(1, 4)]
            + [(i, 2 * i + 3) for i in range(1, 4)]),
        "k4": (4, list(combinations(range(4), 2))),
        "k33": (6, [(u, v) for u in range(3) for v in range(3, 6)]),
        "triangular_prism": (6, [(i, (i + 1) % 3) for i in range(3)]
            + [(i + 3, (i + 1) % 3 + 3) for i in range(3)]
            + [(i, i + 3) for i in range(3)]),
        "cube": (8, [(u, u ^ (1 << j)) for u in range(8) for j in range(3)
                     if u < (u ^ (1 << j))]),
        "petersen": (10, [(i, (i + 1) % 5) for i in range(5)]
            + [(i + 5, (i + 2) % 5 + 5) for i in range(5)]
            + [(i, i + 5) for i in range(5)]),
    }
    output = {
        "all_simple_graphs_through_5_vertices": count,
        "strict_join_savings_in_census": strict,
        "samples": {name: check(*graph) for name, graph in samples.items()},
    }
    support = {(a & b, b, b & c) for a in (0, 1)
               for b in (0, 1) for c in (0, 1)}
    xy = len({(x, y) for x, y, z in support})
    yz = len({(y, z) for x, y, z in support})
    y_only = len({y for x, y, z in support})
    assert (xy, yz, y_only, len(support)) == (3, 3, 2, 5)
    assert xy * yz < y_only * len(support)
    output["nonlinear_support_submodularity_counterexample"] = {
        "left_product": xy * yz, "right_product": y_only * len(support)
    }
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
