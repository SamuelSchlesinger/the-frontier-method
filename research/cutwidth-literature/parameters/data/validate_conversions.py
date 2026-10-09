#!/usr/bin/env python3
"""Validates: small width-conversion examples, joint-boundary accounting, and
the distinction between common-order/state/complete-transition objectives.

These finite checks do not prove any asymptotic or universal bound.
No third-party dependencies; run with Python 3.10 or newer.
"""

from itertools import combinations, permutations, product


def optimum(n, cut):
    """Exact subset DP for min_order max_prefix cut(prefix)."""
    dp = [0] + [10**9] * ((1 << n) - 1)
    for mask in range(1, 1 << n):
        last = mask
        best = 10**9
        while last:
            bit = last & -last
            best = min(best, dp[mask ^ bit])
            last ^= bit
        dp[mask] = max(cut(mask), best)
    return dp[-1]


def graph_cut(edges, mask):
    return sum(((mask >> u) ^ (mask >> v)) & 1 for u, v in edges)


def graph_widths(n, edges):
    adj = [0] * n
    for u, v in edges:
        adj[u] |= 1 << v
        adj[v] |= 1 << u
    full = (1 << n) - 1
    cw = optimum(n, lambda mask: graph_cut(edges, mask))
    pw = optimum(n, lambda mask: sum(
        bool(mask & (1 << v)) and bool(adj[v] & (full ^ mask))
        for v in range(n)))
    return cw, pw


def line_graph(edges):
    return [(i, j) for i, j in combinations(range(len(edges)), 2)
            if set(edges[i]) & set(edges[j])]


def check_graphs():
    examples = [
        ("K2 (exception)", 2, [(0, 1)], (1, 1, 0)),
        ("P3", 3, [(0, 1), (1, 2)], (1, 1, 1)),
        ("triangle", 3, [(0, 1), (1, 2), (2, 0)], (2, 2, 2)),
        ("claw", 4, [(0, 1), (0, 2), (0, 3)], (2, 1, 2)),
        ("K4", 4, list(combinations(range(4), 2)), (4, 3, 4)),
        ("K3,3", 6, [(u, v) for u in range(3) for v in range(3, 6)],
         (5, 3, 5)),
    ]
    print("graph: cutwidth, pathwidth, line-graph pathwidth")
    for name, n, edges, expected in examples:
        cw, pw = graph_widths(n, edges)
        _, line_pw = graph_widths(len(edges), line_graph(edges))
        actual = cw, pw, line_pw
        assert actual == expected, (name, actual, expected)
        assert pw <= cw <= pw + 2
        if len(edges) > 1:
            assert cw == line_pw
        print(f"{name}: {cw}, {pw}, {line_pw}")


def check_joint_boundary():
    # Repeat edges to check that the identity counts multigraph multiplicities.
    edges = [(u, v) for u in range(3) for v in range(3, 6)] + [(0, 3)] * 2
    for parts in product(range(3), repeat=6):
        masks = [sum(1 << v for v, p in enumerate(parts) if p == i)
                 for i in range(3)]
        counts = [graph_cut(edges, mask) for mask in masks]
        union_size = sum(parts[u] != parts[v] for u, v in edges)
        assert 2 * union_size == sum(counts)
        assert 2 * union_size <= 3 * max(counts)
    print("joint boundary: 729 tripartitions with parallel edges passed")


def check_common_order():
    first = [(0, 1), (2, 3)]
    second = [(0, 2), (1, 3)]
    a = optimum(4, lambda mask: graph_cut(first, mask))
    b = optimum(4, lambda mask: graph_cut(second, mask))
    common = optimum(4, lambda mask: max(graph_cut(first, mask),
                                        graph_cut(second, mask)))
    assert (a, b, common) == (1, 1, 2)
    print("common-order gap: separate optima 1, 1; joint optimum 2")


def span(rows):
    result = {0}
    for row in rows:
        result |= {word ^ row for word in result}
    return result


def dim(code):
    size = len(code)
    assert size > 0 and size & (size - 1) == 0
    return size.bit_length() - 1


def code_profiles(n, code, order):
    """Use actual quotient classes of codewords, independent of rank routines."""
    full = (1 << n) - 1
    k = dim(code)
    states = []
    branches = []
    prefix = 0
    for position in range(n + 1):
        suffix = full ^ prefix
        left = {word for word in code if word & suffix == 0}
        right = {word for word in code if word & prefix == 0}
        kernel = {a ^ b for a in left for b in right}
        quotient = {min(word ^ sub for sub in kernel) for word in code}
        state = k - dim(left) - dim(right)
        assert len(quotient) == 1 << state
        states.append(state)
        if position < n:
            bit = 1 << order[position]
            after = suffix ^ bit
            future = {word for word in code if word & (full ^ after) == 0}
            transition_kernel = {a ^ b for a in left for b in future}
            transitions = {min(word ^ sub for sub in transition_kernel)
                           for word in code}
            branch = k - dim(left) - dim(future)
            assert len(transitions) == 1 << branch
            branches.append(branch)
            prefix |= bit
    return max(states), max(branches)


def check_codes():
    examples = [
        ("full binary length 3", span([1, 2, 4]), (0, 1)),
        ("even parity length 3", span([0b011, 0b101]), (1, 2)),
    ]
    for name, code, expected in examples:
        results = {code_profiles(3, code, order)
                   for order in permutations(range(3))}
        assert results == {expected}, (name, results)
        print(f"{name}: max state dimension {expected[0]}, "
              f"max complete-transition dimension {expected[1]}")


if __name__ == "__main__":
    check_graphs()
    check_joint_boundary()
    check_common_order()
    check_codes()
    print("All finite checks passed; no universal improvement asserted.")
