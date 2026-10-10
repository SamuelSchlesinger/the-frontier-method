#!/usr/bin/env python3
"""Exact patch checks and exploratory Gaussian layout screens.

The finite screens do not prove a uniform layout coefficient. The initial field
is a radial polynomial of a finite random cubic graph's adjacency matrix, with
the constant mode removed. It is not the formal high-girth Gaussian construction.
Cut costs and patch minimizations use integers; the initial keys use float64.

Examples:
  python3 research/communication/patch_layout.py --check
  OPENBLAS_NUM_THREADS=1 python3 research/communication/patch_layout.py \
    --vertices 64000 --radius 40 --rounds 128 --seed 1061 --output /tmp/patch.json
"""

import argparse
from itertools import combinations, product
import json
from pathlib import Path
from random import Random
import sys


def cut_size(edges, selected):
    return sum(bool(set(edge) & selected) and not set(edge) <= selected
               for edge in edges)


def largest_minimum(edges, patch, boundary):
    """Independent exact oracle: enumerate every assignment inside the patch."""
    candidates = [set(boundary) | {v for i, v in enumerate(patch) if mask >> i & 1}
                  for mask in range(1 << len(patch))]
    values = [cut_size(edges, candidate) for candidate in candidates]
    best = min(values)
    optimal = [candidate for candidate, value in zip(candidates, values) if value == best]
    largest = set().union(*optimal)
    assert cut_size(edges, largest) == best
    return largest, best


def patch_keys(adj, patch, key):
    """Optimize a connected graph patch with nonempty outside boundary.

    Every cut at an outside key is minimized. Taking the largest minimizer makes
    the chosen subsets nested. New keys are outside-neighbor keys.
    """
    import numpy as np

    index = {v: i for i, v in enumerate(patch)}
    internal, external = [], []
    for i, v in enumerate(patch):
        for w in adj[v]:
            if w in index:
                if i < index[w]:
                    internal.append((i, index[w]))
            else:
                external.append((i, w))
    assert external, "This numerical routine requires a nonempty patch boundary."
    count = 1 << len(patch)
    bits = (np.arange(count)[:, None] >> np.arange(len(patch))[None, :]) & 1
    ext = np.array(external, dtype=np.int32)
    extkeys = key[ext[:, 1]]
    thresholds = np.unique(extkeys)
    internal_cost = np.zeros(count, dtype=np.int64)
    for i, j in internal:
        internal_cost += bits[:, i] != bits[:, j]
    outside = extkeys[None, None, :] <= thresholds[:, None, None]
    costs = internal_cost[None, :] + np.count_nonzero(
        bits[None, :, ext[:, 0]] != outside, axis=2)
    masks = np.bitwise_or.reduce(np.where(
        costs == costs.min(1)[:, None], np.arange(count)[None, :], 0), axis=1)
    assert np.all((masks[:-1] & masks[1:]) == masks[:-1])
    assert masks[-1] == count - 1
    assert np.all(costs[np.arange(len(masks)), masks] == costs.min(1))
    return np.array([thresholds[np.nonzero((masks >> i) & 1)[0][0]]
                     for i in range(len(patch))])


def exact_checks():
    """Uncrossing on all four-vertex hypergraphs; independent key-update oracle."""
    import numpy as np

    possible = [edge for size in (2, 3, 4) for edge in combinations(range(4), size)]
    nested_checks = 0
    minimum_checks = 0
    for graphmask in range(1 << len(possible)):
        edges = [edge for i, edge in enumerate(possible) if graphmask >> i & 1]
        for size in (1, 2, 3):
            patch = list(range(size))
            outside = list(range(size, 4))
            boundaries = [{v for i, v in enumerate(outside) if mask >> i & 1}
                          for mask in range(1 << len(outside))]
            opt = [largest_minimum(edges, patch, boundary)[0] for boundary in boundaries]
            minimum_checks += len(opt)
            for i, earlier in enumerate(boundaries):
                for j, later in enumerate(boundaries):
                    if earlier <= later:
                        assert opt[i] <= opt[j]
                        nested_checks += 1
    edges = [(0, 1), (1, 2), (0, 3), (0, 4), (1, 5), (2, 6), (2, 7)]
    adj = [[] for _ in range(8)]
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    rng = Random(7013102026)
    cases = list(product(range(2), repeat=8))
    cases += [tuple(rng.randrange(3) for _ in range(8)) for _ in range(256)]
    key_checks = 0
    for row in cases:
        key = np.array(row, dtype=np.int64)
        new = key.copy()
        new[:3] = patch_keys(adj, [0, 1, 2], key)
        assert set(new[:3]) <= set(key[3:])
        for t in range(4):
            boundary = {v for v in range(3, 8) if key[v] < t}
            _, best = largest_minimum(edges, [0, 1, 2], boundary)
            actual = {v for v in range(8) if new[v] < t}
            assert cut_size(edges, actual) == best
            key_checks += 1
    return {"hypergraphs": 1 << len(possible), "minimum_checks": minimum_checks,
            "nested_checks": nested_checks, "key_threshold_checks": key_checks}


def radial_field(adj, radius, rng):
    """Finite-graph radial polynomial; subtracting the mean is a global operation."""
    import numpy as np
    from scipy.linalg import eigh_tridiagonal

    _, eigenvectors = eigh_tridiagonal(
        np.zeros(radius + 1), np.r_[np.sqrt(3), np.full(radius - 1, np.sqrt(2))],
        select="i", select_range=(radius, radius))
    coeff = eigenvectors[:, 0] * np.sign(eigenvectors[0, 0])
    previous = rng.standard_normal(len(adj))
    previous -= previous.mean()
    field = coeff[0] * previous
    current = previous[adj].sum(1) / np.sqrt(3)
    current -= current.mean()
    field += coeff[1] * current
    for k in range(2, radius + 1):
        earlier_weight = np.sqrt(3) if k == 2 else np.sqrt(2)
        later = (current[adj].sum(1) - earlier_weight * previous) / np.sqrt(2)
        later -= later.mean()
        field += coeff[k] * later
        previous, current = current, later
    return field


def profile(adj, edges, key, step):
    import numpy as np

    n = len(adj)
    order = np.argsort(key, kind="stable")
    position = np.empty(n, dtype=np.int32)
    position[order] = np.arange(n)
    delta = 3 - 2 * (position[adj] < position[:, None]).sum(1)
    cuts = np.cumsum(delta[order])
    group_end = np.r_[key[order[:-1]] != key[order[1:]], True]
    group_starts = np.r_[0, np.nonzero(group_end)[0] + 1]
    zero = np.count_nonzero((key[edges[:, 0]] < 0) != (key[edges[:, 1]] < 0))
    return {"round": step, "zero": float(zero / n),
            "peak_threshold": float(cuts[group_end].max() / n),
            "peak_prefix": float(cuts.max() / n),
            "max_tie": int(np.diff(group_starts).max())}


def screen(n, radius, rounds, seed):
    import networkx as nx
    import numpy as np

    rng = np.random.default_rng(seed)
    graph = nx.random_regular_graph(3, n, seed=seed)
    adj = np.array([list(graph[v]) for v in range(n)], dtype=np.int32)
    edges = np.array(list(graph.edges()), dtype=np.int32)
    field = radial_field(adj, radius, rng)
    correlation = np.mean(field[edges[:, 0]] * field[edges[:, 1]]) / np.mean(field * field)
    key = field + np.median(field[adj], axis=1)
    rows = [profile(adj, edges, key, 0)]
    previous_peak = rows[0]["peak_threshold"]
    previous_zero = rows[0]["zero"]
    for step in range(1, rounds + 1):
        priorities = rng.random(n)
        local_minimum = priorities.copy()
        for _ in range(3):
            local_minimum = np.minimum(local_minimum, local_minimum[adj].min(1))
        # Centers have distance at least four: their radius-one patches are
        # disjoint and have no edge between them. Each update reads unchanged keys.
        centers = np.nonzero(priorities == local_minimum)[0]
        patches = [[v, *rng.choice(adj[v], size=2, replace=False)] for v in centers]
        selected = {w for patch in patches for w in patch}
        assert len(selected) == 3 * len(patches)
        for patch in patches:
            assert all(w not in selected or w in patch for v in patch for w in adj[v])
            key[patch] = patch_keys(adj, patch, key)
        if step & (step - 1) == 0 or step == rounds:
            row = profile(adj, edges, key, step)
            assert row["peak_threshold"] <= previous_peak
            assert row["zero"] <= previous_zero
            previous_peak, previous_zero = row["peak_threshold"], row["zero"]
            rows.append(row)
            print(json.dumps({"seed": seed, **row}), file=sys.stderr, flush=True)
    return {"vertices": n, "radius": radius, "rounds": rounds, "seed": seed,
            "edge_correlation": float(correlation), "rows": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--vertices", type=int, default=16000)
    parser.add_argument("--radius", type=int, default=20)
    parser.add_argument("--rounds", type=int, default=128)
    parser.add_argument("--seed", type=int, default=1049)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.check:
        result = exact_checks()
    else:
        if args.vertices < 8 or args.vertices % 2 or args.radius < 2 or args.rounds < 1:
            parser.error("Use an even vertex count >= 8, radius >= 2, and positive rounds.")
        result = screen(args.vertices, args.radius, args.rounds, args.seed)
    rendered = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
