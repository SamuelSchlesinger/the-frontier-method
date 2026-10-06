#!/usr/bin/env python3
"""Check unique additive generation and disjoint direct-sumset peeling.

Finite evidence only. The all-size weighted theorem is in Lean; the complete
circuit-to-generator construction remains a paper proof.
"""

from collections import Counter, defaultdict
from pathlib import Path
from random import Random
import sys

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import syndrome_generator as sg


def path_sums(edges, start, finish, banned):
    """Independently count prefix/suffix paths in an explicitly layered graph."""
    nodes = sorted({start, finish} | {u for u, _, _ in edges} | {v for _, v, _ in edges},
                   key=lambda v: v[0])
    outgoing = defaultdict(list)
    for u, v, label in edges:
        if u not in banned and v not in banned:
            outgoing[u].append((v, label))
    prefixes, suffixes = defaultdict(Counter), defaultdict(Counter)
    if start not in banned:
        prefixes[start][0] = 1
    for u in nodes:
        for v, label in outgoing[u]:
            for value, count in prefixes[u].items():
                prefixes[v][value ^ label] += count
    if finish not in banned:
        suffixes[finish][0] = 1
    for u in reversed(nodes):
        for v, label in outgoing[u]:
            for value, count in suffixes[v].items():
                suffixes[u][value ^ label] += count
    return nodes, prefixes, suffixes


def check_peeling(edge_layers, code, expected, threshold, n, rng):
    _, syndrome, _, translation, kernel = code
    edges = []
    for layer, transitions in enumerate(edge_layers):
        edges.extend(((layer, u), (layer + 1, v), label) for u, v, label in transitions)
    layer = len(edge_layers)
    last = (layer, ((), syndrome))
    tail = (layer + 1, "tail")
    edges.append((last, tail, translation))
    layer += 1
    for vector in kernel:
        nxt = (layer + 1, "tail")
        edges.extend([(tail, nxt, 0), (tail, nxt, vector)])
        tail = nxt
        layer += 1
    start, finish = (0, ((), 0)), tail
    banned, removed, blocks = set(), set(), []
    while True:
        nodes, prefixes, suffixes = path_sums(edges, start, finish, banned)
        assert dict(prefixes[finish]) == {x: 1 for x in expected - removed}
        choices = [v for v in nodes
                   if len(prefixes[v]) >= threshold and len(suffixes[v]) >= threshold]
        if not choices:
            break
        vertex = rng.choice(choices)
        left, right = set(prefixes[vertex]), set(suffixes[vertex])
        assert set(prefixes[vertex].values()) == {1}
        assert set(suffixes[vertex].values()) == {1}
        sums = Counter(a ^ b for a in left for b in right)
        assert len(sums) == len(left) * len(right) and set(sums.values()) == {1}
        block = set(sums)
        assert not block & removed
        blocks.append(block)
        removed |= block
        banned.add(vertex)
    residual = expected - removed
    assert len(residual) <= (threshold - 1) ** 2 * len(edges)
    for _ in range(8):
        signs = [rng.choice((-1, 1)) for _ in range(1 << n)]
        # This budget controls the actual peeled blocks. It is not a claim that
        # these random signs are an extractor for every possible source pair.
        bias = max([abs(sum(signs[x] for x in block)) / len(block) for block in blocks] or [0])
        actual = abs(sum(signs[x] for x in expected))
        assert actual <= bias * len(removed) + len(residual) + 1e-9
        assert actual <= bias * len(expected) + (threshold - 1) ** 2 * len(edges) + 1e-9
    return len(blocks)


class OutputNetwork(sg.Network):
    """Enforce either output bit; the base Network's False flag is unconstrained."""

    def __init__(self, n, gates, out, wanted):
        super().__init__(n, gates, [(out, True)])
        self.wanted = wanted

    def check(self, vertex, value, input_bit):
        if vertex[0] == "out":
            return value(self.ports[vertex, 0]) == self.wanted
        return super().check(vertex, value, input_bit)


def main():
    # Negative control: ambiguity breaks the direct-sumset cardinal identity.
    ambiguous = Counter(a ^ b for a in (0, 1) for b in (0, 1))
    assert ambiguous == {0: 2, 1: 2} and len(ambiguous) < 2 * 2
    rng = Random(61006)
    instances = paths = blocks = 0
    for trial in range(36):
        n, m = rng.randrange(1, 7), rng.randrange(2, 7)
        rows = [rng.randrange(1 << n) for _ in range(m)]
        offsets = [rng.randrange(2) for _ in rows]
        gates = [sg.Gate(rng.randrange(16), (0, 1))]
        for j in range(2, m):
            gates.append(sg.Gate(rng.randrange(16), (m + len(gates) - 1, j)))
        for _ in range(2):
            gates.append(sg.Gate(rng.randrange(16),
                                 (m + len(gates) - 1, rng.randrange(m + len(gates)))))
        out = m + len(gates) - 1
        code = sg.affine_code(n, rows, offsets)
        ones = sg.direct_support(n, rows, offsets, gates, out)
        for bit in (False, True):
            net = OutputNetwork(m, gates, out, bit)
            expected = ones if bit else set(range(1 << n)) - ones
            for _ in range(2):
                order = list(net.vertices)
                rng.shuffle(order)
                for pruning, joint in ((False, False), (True, False), (True, True)):
                    actual, _, _, edge_layers = sg.generated_paths(
                        net, order, *code, prune_syndrome=pruning, joint=joint)
                    assert dict(actual) == {x: 1 for x in expected}, (trial, bit, actual, expected)
                    for threshold in (2, 3, 4):
                        blocks += check_peeling(edge_layers, code, expected, threshold, n, rng)
                    paths += sum(actual.values())
                    instances += 1
    print(f"{instances} compiled generators: exact path multiplicity 1 "
          f"on all {paths} accepted inputs.")
    print(f"{3 * instances} peeling runs, {blocks} disjoint direct-sumset blocks; "
          "residual and signed-sum bounds passed.")


if __name__ == "__main__":
    main()
