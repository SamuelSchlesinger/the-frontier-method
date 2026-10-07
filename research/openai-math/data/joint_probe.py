#!/usr/bin/env python3
"""Validates: complete-transition costs and restriction savings on the same circuits.

Exact truth tables are the oracle for the existing compiler and normalizer.
Three explicitly chosen layouts are compared; they are not optimal layouts.
All four examples compute easy functions, not the hard extractor family.
This is a diagnostic of mechanisms, not evidence for a universal coefficient.
"""

from collections import Counter
from itertools import product
from math import acos, log2, pi, sqrt
from pathlib import Path
import json
import sys

sys.dont_write_bytecode = True
REPO = Path(__file__).resolve().parents[3]
sys.path[:0] = [str(REPO / "scripts"), str(REPO / "research/communication")]
from check_algorithms import Gate, Network
from check_communication import traces
from restrictions import Circuit, Literal


def examples():
    def combine(n, gates, wires):
        value = wires[0]
        for wire in wires[1:]:
            gates[n + len(gates)] = (6, value, wire)
            value = n + len(gates) - 1
        return Circuit(n, gates, Literal(value))

    yield "parity", combine(6, {}, list(range(6)))
    yield "independent_masks", combine(8, {8+i: (8, 2*i, 2*i+1) for i in range(4)},
                                       list(range(8, 12)))
    yield "shared_selector", combine(7, {7+i: (8, 0, i+1) for i in range(6)},
                                     list(range(7, 13)))
    gates = {6+i: (6, i, (i+1) % 6) for i in range(6)}
    gates.update({12+i: (8, 6+2*i, 7+2*i) for i in range(3)})
    yield "cycle_parities", combine(6, gates, list(range(12, 15)))


def compiled(circuit):
    remap = {i: i for i in range(circuit.n)}
    gates = []
    for w, (op, a, b) in sorted(circuit.gates.items()):
        remap[w] = circuit.n + len(gates)
        gates.append(Gate(op, (remap[a], remap[b])))
    assert circuit.output.wire is not None
    out = remap[circuit.output.wire]
    return gates, out, Network(circuit.n, gates, [(out, False)])


def greedy_order(net):
    def cut(past):
        return {w for u, v, w in net.edges if (u in past) != (v in past)}
    past, order = set(), []
    while len(order) < len(net.vertices):
        before = cut(past)
        vertex = min((v for v in net.vertices if v not in past),
                     key=lambda v: (len(before | cut(past | {v})), repr(v)))
        order.append(vertex)
        past.add(vertex)
    return order


def tree_order(net):
    """Postorder of a DFS tree, processing larger child subtrees first."""
    adjacent = {v: set() for v in net.vertices}
    for u, v, _ in net.edges:
        adjacent[u].add(v)
        adjacent[v].add(u)
    seen = set()

    def visit(v):
        seen.add(v)
        children = [visit(u) for u in sorted(adjacent[v], key=repr) if u not in seen]
        children.sort(key=len, reverse=True)
        return [u for child in children for u in child] + [v]

    result = visit(("out", 0))
    assert len(result) == len(net.vertices)
    return result


def main():
    A = 3 / pi * acos((1 + 2 * sqrt(2)) / 4)
    L = 1 + 1 / A
    report = []
    checked = 0
    for name, original in examples():
        circuit = original.normalize()
        words = list(product((0, 1), repeat=circuit.n))
        assert all(original.evaluate(x) == circuit.evaluate(x) for x in words)
        gates, out, net = compiled(circuit)
        sizes = []
        for order in (net.vertices, greedy_order(net), tree_order(net)):
            rows = traces(circuit.n, gates, out, net, order)
            assert all((row[0][0] ^ circuit.output.neg) == original.evaluate(x)
                       for row, x in zip(rows, words))
            hist = [Counter(row[t] for row in rows) for t in range(len(rows[0]))]
            # These labels retain the output class and the complete signal code.
            peak_support = max(log2(len(h)) for h in hist)
            peak_half = max(2 * log2(sum(sqrt(count / len(words)) for count in h.values()))
                            for h in hist)
            assert peak_half <= peak_support + 1e-10
            sizes.append({"peak_support_bits": peak_support, "peak_half_bits": peak_half})
        choices = []
        for i in range(circuit.n):
            for bit in (0, 1):
                restricted = circuit.normalize({i: bit})
                assert all(restricted.evaluate(x) == original.evaluate(x)
                           for x in words if x[i] == bit)
                saved = len(circuit.gates) - len(restricted.gates)
                choices.append((saved, i, bit))
                checked += 1
        saved, i, bit = max(choices)
        report.append({
            "name": name, "inputs": circuit.n, "normalized_gates": len(circuit.gates),
            "best_of_three_peak_support_bits": round(min(s["peak_support_bits"] for s in sizes), 6),
            "best_of_three_peak_half_bits": round(min(s["peak_half_bits"] for s in sizes), 6),
            "best_restriction": {"input": i, "value": bit, "gates_saved": saved,
                                 "dimension_lost": 1, "surplus_over_L": round(saved - L, 6)},
        })
    print(json.dumps({"circuits": report, "truth_table_restriction_checks": checked,
                      "layouts_per_circuit": 3,
                      "scope": "diagnostic only; no target-hardness or structural coverage claim"},
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
