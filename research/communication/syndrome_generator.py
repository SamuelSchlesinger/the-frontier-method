#!/usr/bin/env python3
"""Exact additive generation through a coded affine interface.

Small-instance oracle: generated inputs must equal the original circuit's full
truth-table support. All code constraints and local gate equations are retained.
This checks the compiler, not a universal improvement of the circuit coefficient.
"""

from collections import defaultdict
from itertools import product
from pathlib import Path
from random import Random
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "scripts"))
from check_algorithms import Gate, Network
from restrictions import affine_basis, parity


def inverse_rows(rows, n):
    augmented = [row | (1 << (n + i)) for i, row in enumerate(rows)]
    for col in range(n):
        pivot = next(i for i in range(col, n) if (augmented[i] >> col) & 1)
        augmented[col], augmented[pivot] = augmented[pivot], augmented[col]
        for i in range(n):
            if i != col and (augmented[i] >> col) & 1:
                augmented[i] ^= augmented[col]
    assert all(row & ((1 << n) - 1) == 1 << i for i, row in enumerate(augmented))
    return [row >> n for row in augmented]


def affine_code(n, rows, offsets):
    """Parity-check columns, syndrome, a linear section, and a kernel basis."""
    basis, selected, expressions = affine_basis(rows)
    full_basis, _, _ = affine_basis(basis + [1 << i for i in range(n)])
    inverse = inverse_rows(full_basis, n)
    inverse_columns = [sum(((row >> j) & 1) << i for i, row in enumerate(inverse))
                       for j in range(n)]
    selected_position = {j: i for i, j in enumerate(selected)}
    dependent = [j for j in range(len(rows)) if j not in selected_position]
    checks = [0] * len(rows)
    for k, j in enumerate(dependent):
        checks[j] ^= 1 << k
        for i, index in enumerate(selected):
            if (expressions[j] >> i) & 1:
                checks[index] ^= 1 << k
    labels = [inverse_columns[selected_position[j]] if j in selected_position else 0
              for j in range(len(rows))]
    syndrome = translation = 0
    for bit, check, label in zip(offsets, checks, labels):
        if bit:
            syndrome ^= check
            translation ^= label
    return checks, syndrome, labels, translation, inverse_columns[len(basis):]


def span(vectors):
    values = {0}
    for vector in vectors:
        values |= {x ^ vector for x in values}
    return values


def feasible_syndromes(checks, read, target):
    """Exact extendable partial syndromes and the independent rank formula."""
    left = [check for j, check in enumerate(checks) if j in read]
    right = [check for j, check in enumerate(checks) if j not in read]
    feasible = span(left) & {target ^ value for value in span(right)}
    dimension = (len(affine_basis(left)[0]) + len(affine_basis(right)[0])
                 - len(affine_basis(checks)[0]))
    # The affine code is nonempty, so the slice is a translate of the intersection.
    assert len(feasible) == 1 << dimension
    return feasible, dimension


def generated_support(net, order, checks, syndrome, labels, translation, kernel,
                      prune_syndrome=True, omit_code_check=False):
    """Union/translation DP over boundary assignments and one syndrome register."""
    assert net.unread == 0
    assert len(order) == len(net.vertices) and set(order) == set(net.vertices)
    if omit_code_check:
        prune_syndrome = False
    past, previous_cut = set(), []
    read = set()
    table = {((), 0): {0}}
    edge_count = 0
    layers = []
    c = max(checks, default=0).bit_length()
    for vertex in order:
        feasible, dimension = feasible_syndromes(checks, read, syndrome)
        if prune_syndrome:
            assert all(state[1] in feasible for state in table)
        past.add(vertex)
        next_cut = [e for e, (u, v, _) in enumerate(net.edges)
                    if (u in past) != (v in past)]
        old_edges = set(previous_cut)
        incident = net.incident[vertex]
        fresh = sorted(set(incident) - old_edges)
        is_input = vertex[0] == "wire" and vertex[1] < net.n
        if is_input:
            read.add(vertex[1])
        next_feasible, _ = feasible_syndromes(checks, read, syndrome)
        updated = defaultdict(set)
        transitions = set()
        for before, vectors in table.items():
            old_values = dict(zip(previous_cut, before[0]))
            for bits in product((0, 1), repeat=len(fresh)):
                assignment = old_values | dict(zip(fresh, bits))
                for bit in (0, 1) if is_input else (0,):
                    if not net.check(vertex, assignment.__getitem__, bit):
                        continue
                    addition = labels[vertex[1]] if is_input and bit else 0
                    change = checks[vertex[1]] if is_input and bit else 0
                    after = (tuple(assignment[e] for e in next_cut), before[1] ^ change)
                    if prune_syndrome and after[1] not in next_feasible:
                        continue
                    transitions.add((before, after, addition))
                    updated[after].update(x ^ addition for x in vectors)
        # One old syndrome determines the new one from the read value. There
        # is no second independent syndrome assignment in this count.
        budget = 1 << ((dimension if prune_syndrome else c)
                       + len(old_edges | set(next_cut)) + int(is_input))
        assert len(transitions) <= budget
        layers.append((len(transitions), budget))
        edge_count += len(transitions)
        table, previous_cut = updated, next_cut
    if omit_code_check:
        values = set().union(*table.values()) if table else set()
    else:
        values = table.get(((), syndrome), set())
    values = {x ^ translation for x in values}
    for vector in kernel:
        values |= {x ^ vector for x in values}
    return values, edge_count + 1 + 2 * len(kernel), layers


def direct_support(n, rows, offsets, gates, out):
    accepted = set()
    for x in range(1 << n):
        values = [parity(row & x) ^ bit for row, bit in zip(rows, offsets)]
        for gate in gates:
            values.append(gate.evaluate(values))
        if values[out]:
            accepted.add(x)
    return accepted


def check_compiler():
    rng = Random(510)
    cases = checked = 0
    for _ in range(24):
        n, m = rng.randrange(1, 6), rng.randrange(2, 7)
        rows = [rng.randrange(1 << n) for _ in range(m)]
        offsets = [rng.randrange(2) for _ in rows]
        # Every interface signal is syntactically reachable, including with
        # degenerate gate truth tables. Later gates can reuse earlier signals.
        gates = [Gate(rng.randrange(16), (0, 1))]
        for j in range(2, m):
            gates.append(Gate(rng.randrange(16), (m + len(gates) - 1, j)))
        for _ in range(2):
            gates.append(Gate(rng.randrange(16),
                              (m + len(gates) - 1, rng.randrange(m + len(gates)))))
        out = m + len(gates) - 1
        expected = direct_support(n, rows, offsets, gates, out)
        code = affine_code(n, rows, offsets)
        net = Network(m, gates, [(out, True)])
        for reverse in (False, True):
            order = list(net.vertices)
            if reverse:
                order.reverse()
            else:
                rng.shuffle(order)
            for pruning in (False, True):
                actual, edges, layers = generated_support(net, order, *code,
                                                          prune_syndrome=pruning)
                assert actual == expected, (n, rows, offsets, gates, expected, actual)
                assert edges <= sum(budget for _, budget in layers) + 1 + 2 * len(code[-1])
            checked += 1
        cases += 1
    print(f"Syndrome generator: {cases} coded circuits, {checked} arbitrary layouts "
          "matched truth-table supports and budgets with global and trellis states.")


def components(n, edges):
    parent = list(range(n))

    def root(v):
        while parent[v] != v:
            v = parent[v]
        return v

    for u, v in edges:
        parent[root(u)] = root(v)
    return len({root(v) for v in range(n)})


def check_graphic_profiles():
    # K4 is cubic; the wheel is irregular. Every bipartition is checked, including
    # disconnected spanning sides, so cycle rank must include all components.
    graphs = [(4, [(u, v) for u in range(4) for v in range(u + 1, 4)]),
              (5, [(u, 4) for u in range(4)] + [(u, (u + 1) % 4) for u in range(4)])]
    checked = 0
    for n, edges in graphs:
        rows = [(1 << u) | (1 << v) for u, v in edges]
        checks, target, *_ = affine_code(n, rows, [j % 2 for j in range(len(rows))])
        c = len(edges) - n + 1
        for mask in range(1 << len(edges)):
            read = {j for j in range(len(edges)) if mask & (1 << j)}
            left = [edge for j, edge in enumerate(edges) if j in read]
            right = [edge for j, edge in enumerate(edges) if j not in read]
            _, dimension = feasible_syndromes(checks, read, target)
            left_cycles = len(left) - n + components(n, left)
            right_cycles = len(right) - n + components(n, right)
            assert dimension == c - left_cycles - right_cycles
            checked += 1
    print(f"Graphic profiles: {checked} edge bipartitions matched exact syndrome "
          "cardinalities and the componentwise cycle formula.")


def check_missing_constraint():
    # The code is y=(x,x). The suffix y0 XOR y1 is always zero on the code.
    # Omitting the final syndrome test creates false accepting original inputs.
    rows, offsets, gates = [1, 1], [0, 0], [Gate(6, (0, 1))]
    net = Network(2, gates, [(2, True)])
    code = affine_code(1, rows, offsets)
    correct, _, _ = generated_support(net, list(net.vertices), *code)
    incorrect, _, _ = generated_support(net, list(net.vertices), *code, omit_code_check=True)
    assert correct == direct_support(1, rows, offsets, gates, 2) == set()
    assert incorrect == {0, 1}
    print("Constraint-removal guard: omitting the syndrome creates two false accepted inputs.")


if __name__ == "__main__":
    check_compiler()
    check_graphic_profiles()
    check_missing_constraint()
