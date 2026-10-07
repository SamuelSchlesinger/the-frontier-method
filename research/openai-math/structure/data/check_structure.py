#!/usr/bin/env python3
"""Validates: critical Ising cuts and one median pass miss the Gaussian budget;
thin-tree cuts do not bound original cuts; L1 cuts need not be compatible.

Python standard library only. These are arithmetic and finite graph checks,
not a verification of an upstream theorem or a universal layout improvement.
The Ising calculation uses the exact free-tree star law described in family
236; the transfer to finite cubic graphs is deliberately not assumed proved.
Source/provenance and the scope of every deduction are in ../index.md.
"""

from itertools import product
from math import acos, isclose, pi, sqrt


def cut(edges, region):
    return {edge for edge in edges if (edge[0] in region) != (edge[1] in region)}


def prism(m):
    """C_m square K_2 and a Hamiltonian path with one edge between its layers."""
    assert m >= 3
    edges = set()
    for layer in range(2):
        for i in range(m):
            edges.add(tuple(sorted((layer * m + i, layer * m + (i + 1) % m))))
    edges.update((i, m + i) for i in range(m))
    order = list(range(m)) + list(range(2 * m - 1, m - 1, -1))
    tree = {tuple(sorted(pair)) for pair in zip(order, order[1:])}
    assert tree <= edges and len(tree) == 2 * m - 1
    assert all(sum(v in e for e in edges) == 3 for v in range(2 * m))
    return edges, tree


def check_ising():
    theta = 1 / sqrt(2)
    p = (1 - theta) / 2
    gaussian = (3 / pi) * acos((1 + 2 * sqrt(2)) / 4)
    gain = 0.0
    mass = 0.0
    # By spin symmetry fix the root spin to +1. The three disagreement bits
    # are independent in the free-tree law, even though stars are not.
    for bits in product((0, 1), repeat=3):
        k = sum(bits)
        probability = p**k * (1 - p) ** (3 - k)
        before = k
        after = min(k, 3 - k)
        assert before - after == max(0, 2 * k - 3)
        gain += probability * (before - after)
        mass += probability
    assert isclose(mass, 1.0)
    assert isclose(gain, 3 * p * p)
    one_cut = 3 * p
    quarter_pass = one_cut - gain / 2
    # An adaptively chosen independent set still saves at most the sum of
    # all nonnegative star gains. For h cubic vertices, beta_1 ~ h/2.
    adaptive_pass_lower = one_cut - 2 * gain
    assert adaptive_pass_lower > gaussian
    threshold_needed = 1 - 2 * gaussian / 3
    assert threshold_needed > theta
    print(f"gaussian_cycle_rank_A={gaussian:.12f}")
    print(f"frontier_gate_L={1 + 1 / gaussian:.12f}")
    print(f"critical_ising_p={p:.12f}")
    print(f"critical_ising_one_cut_proxy={one_cut:.12f}")
    print(f"required_ising_theta_to_beat_A={threshold_needed:.12f}")
    print(f"star_expected_median_gain={gain:.12f}")
    print(f"quarter_density_independent_pass_proxy={quarter_pass:.12f}")
    print(f"any_one_independent_pass_mean_proxy_lower={adaptive_pass_lower:.12f}")
    print(f"ramanujan_spectral_bisection_proxy={(3 - 2 * sqrt(2)) / 2:.12f}")


def check_prisms():
    checked = 0
    for m in range(3, 8):
        edges, tree = prism(m)
        minimum_cut = len(edges)
        for mask in range(1, (1 << (2 * m)) - 1):
            region = {v for v in range(2 * m) if (mask >> v) & 1}
            original = len(cut(edges, region))
            selected = len(cut(tree, region))
            assert selected <= original  # All-cut thinness with C=k=3.
            assert selected >= 1
            minimum_cut = min(minimum_cut, original)
            checked += 1
        assert minimum_cut == 3
        top = set(range(m))
        assert len(cut(tree, top)) == 1
        assert len(cut(edges, top)) == m
        print(f"prism_m={m}: connectivity=3, layer_cut_tree=1, layer_cut_graph={m}")
    print(f"prism_nontrivial_cuts_checked={checked}")


def check_cut_geometry():
    points = ((0, 0), (1, 0), (1, 1), (0, 1))
    cuts = ({1, 2}, {2, 3})
    universe = set(range(4))
    a, b = cuts
    assert a & b and a - b and b - a and universe - (a | b)
    for u, v in product(range(4), repeat=2):
        distance = min(abs(u - v), 4 - abs(u - v))
        l1 = sum(abs(x - y) for x, y in zip(points[u], points[v]))
        cut_metric = sum((u in region) != (v in region) for region in cuts)
        assert distance == l1 == cut_metric
    print("C4_isometric_L1_cut_family=crossing (not laminar)")
    edges = {(0, 1), (0, 2), (1, 2)}
    left, right = {0}, {1}
    c1, c2, cp = (cut(edges, r) for r in (left, right, left | right))
    assert 2 * len(c1 | c2) == len(c1) + len(c2) + len(cp)
    assert max(len(c1), len(c2), len(cp)) == 2 and len(c1 | c2) == 3
    print("triangle_individual_boundary_max=2, joint_merge=3")


if __name__ == "__main__":
    check_ising()
    check_prisms()
    check_cut_geometry()
    print("OK: finite checks passed; no universal layout theorem inferred")
