#!/usr/bin/env python3
"""Validates: spectral target arithmetic, entropy barrier, exact median charge
identity, and finite examples of threshold-coherent patch minimization.

Standard library only. These checks are not an asymptotic cutwidth certificate.
The patch theorem has an independent submodularity proof in ../patches.md.
The spectral/entropy calculations are deductions from the cited theorems in
../index.md; the script does not certify their hypotheses for a new process.
"""

from itertools import combinations, permutations, product
from math import acos, cos, log, log2, pi, sqrt
import json


def cut(edges, chosen):
    return sum((u in chosen) != (v in chosen) for u, v in edges)


def subsets(vertices):
    vertices = tuple(vertices)
    return [frozenset(v for i, v in enumerate(vertices) if mask >> i & 1)
            for mask in range(1 << len(vertices))]


def binary_entropy(q):
    if q == 0 or q == 1:
        return 0.0
    return -q * log2(q) - (1 - q) * log2(1 - q)


def arithmetic():
    rho = 2 * sqrt(2) / 3
    p = 3 / (2 * pi) * acos((1 + 3 * rho) / 4)
    lo, hi = 0.0, 0.5
    for _ in range(100):
        mid = (lo + hi) / 2
        if binary_entropy(mid) < 1 / 3:
            lo = mid
        else:
            hi = mid
    result = {
        'baseline_p': p,
        'baseline_circuit_coefficient': 1 + 1 / (2 * p),
        'vertex_gaussian_p': 3 / (2 * pi) * acos(rho),
        'tree_neighbor_correlation': rho,
        'correlation_needed_for_p_one_eighth_in_same_star_formula':
            (4 * cos(pi / 12) - 1) / 3,
        'gain_per_vertex_needed_for_p_one_eighth': p - 1 / 8,
        'threshold_band_for_p_one_eighth': sqrt(2 * log(p / (1 / 8))),
        'mean_local_gain_needed_if_selected_with_probability_one_quarter':
            4 * (p - 1 / 8),
        'entropy_crossing_probability_lower_bound': (lo + hi) / 2,
        'entropy_cut_coefficient_lower_bound': 1.5 * (lo + hi) / 2,
        'Harangi_maxcut_complement_density_for_degree_three':
            1.5 * (1 - 0.92386),
    }
    assert result['correlation_needed_for_p_one_eighth_in_same_star_formula'] > rho
    assert result['entropy_cut_coefficient_lower_bound'] < 1 / 8
    return result


def verify_charge_identity():
    # Every Boolean edge assignment on these cubic graphs checks every possible
    # threshold sign pattern, not samples from a Gaussian distribution.
    graphs = {
        'K4': list(combinations(range(4), 2)),
        'K3,3': [(u, v) for u in range(3) for v in range(3, 6)],
        'triangular_prism': [(0, 1), (1, 2), (2, 0), (3, 4), (4, 5),
                             (5, 3), (0, 3), (1, 4), (2, 5)],
    }
    checked = 0
    for edges in graphs.values():
        vertices = sorted({v for e in edges for v in e})
        incidence = {v: [i for i, e in enumerate(edges) if v in e] for v in vertices}
        assert all(len(incidence[v]) == 3 for v in vertices)
        for bits in product((0, 1), repeat=len(edges)):
            color = {v: sum(bits[i] for i in incidence[v]) >= 2 for v in vertices}
            straddlers = sum(len({bits[i] for i in incidence[v]}) == 2 for v in vertices)
            crossing = sum(color[u] != color[v] for u, v in edges)
            double_minority = sum(bits[i] != color[u] and bits[i] != color[v]
                                  for i, (u, v) in enumerate(edges))
            assert straddlers == crossing + 2 * double_minority
            checked += 1
    return checked


def verify_patch_minimizers():
    # Enumerate all simple graphs on five labeled vertices with degree <= 3,
    # a fixed two-vertex interior, and every strict ordering of boundary keys.
    # Each interior vertex must reach the boundary, so the extreme minimizers
    # are respectively empty and full, without unconstrained components.
    n = 5
    possible_edges = list(combinations(range(n), 2))
    interior = frozenset((0, 1))
    boundary = frozenset((2, 3, 4))
    choices = subsets(interior)
    graphs = thresholds = 0
    for graph_bits in product((0, 1), repeat=len(possible_edges)):
        all_edges = [e for bit, e in zip(graph_bits, possible_edges) if bit]
        if any(sum(v in e for e in all_edges) > 3 for v in range(n)):
            continue
        # Boundary-boundary edges are constant in each local optimization.
        edges = [e for e in all_edges if interior.intersection(e)]
        reached = set(boundary)
        while True:
            new = reached | {v for u, v in edges if u in reached} | {
                u for u, v in edges if v in reached}
            if new == reached:
                break
            reached = new
        if not interior <= reached:
            continue
        graphs += 1
        for ordering in permutations(boundary):
            previous = frozenset()
            for j in range(len(boundary) + 1):
                selected_boundary = frozenset(ordering[:j])
                values = [(cut(edges, s | selected_boundary), s) for s in choices]
                optimum = min(value for value, _ in values)
                minimizers = [s for value, s in values if value == optimum]
                maximal = frozenset().union(*minimizers)
                assert maximal in minimizers
                assert previous <= maximal
                if j == 0:
                    assert maximal == frozenset()
                if j == len(boundary):
                    assert maximal == interior
                for original in choices:
                    assert cut(edges, maximal | selected_boundary) <= cut(
                        edges, original | selected_boundary)
                previous = maximal
                thresholds += 1
    return {'graphs': graphs, 'threshold_instances': thresholds}


if __name__ == '__main__':
    print(json.dumps({
        'status': 'finite checks and floating-point arithmetic only',
        'arithmetic': arithmetic(),
        'median_charge_boolean_assignments': verify_charge_identity(),
        'patch_minimizers': verify_patch_minimizers(),
    }, indent=2, sort_keys=True))
