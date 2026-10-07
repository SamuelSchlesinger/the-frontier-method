#!/usr/bin/env python3
"""Validates: returns affect two-way splicing, and linear dirty replay fails for AND.

The diagram convention and linear replay identity are from OpenAI families 129
and 130 at adc7f1241b42e322a6451854ab7e4b4c146bf78a. See ../index.md for
exact sources. The examples and exhaustive finite checks below are local
deductions; they do not verify either upstream theorem or an asymptotic compiler.
"""

from dataclasses import dataclass
from itertools import product


def compose(a, b):
    """Relations in path order: a then b."""
    return frozenset((x, z) for x, y in a for y2, z in b if y == y2)


def star(a, m):
    answer = a | frozenset((x, x) for x in range(m))
    while True:
        larger = answer | compose(answer, answer)
        if larger == answer:
            return answer
        answer = larger


@dataclass(frozen=True)
class Diagram:
    forward: frozenset
    backward: frozenset
    left: frozenset
    right: frozenset


def multiply(a, b, m):
    lr = star(compose(b.left, a.right), m)
    rl = star(compose(a.right, b.left), m)
    return Diagram(
        compose(compose(a.forward, lr), b.forward),
        compose(compose(b.backward, rl), a.backward),
        a.left | compose(compose(compose(a.forward, lr), b.left), a.backward),
        b.right | compose(compose(compose(b.backward, a.right), lr), b.forward),
    )


def joined_forward(a, b):
    """Independent graph-reachability oracle on the joined boundary ports."""
    edges = set()
    for side, d in enumerate((a, b)):
        for x, y in d.forward:
            edges.add(((side, "+", x), (side + 1, "+", y)))
        for x, y in d.backward:
            edges.add(((side + 1, "-", x), (side, "-", y)))
        for x, y in d.left:
            edges.add(((side, "+", x), (side, "-", y)))
        for x, y in d.right:
            edges.add(((side + 1, "-", x), (side + 1, "+", y)))
    answer = set()
    for start in range(2):
        reached = {(0, "+", start)}
        pending = list(reached)
        while pending:
            node = pending.pop()
            # A first outer exit ends the path.
            if node[0:2] in ((0, "-"), (2, "+")):
                continue
            for src, dst in edges:
                if src == node and dst not in reached:
                    reached.add(dst)
                    pending.append(dst)
        answer.update((start, q) for boundary, sign, q in reached
                      if boundary == 2 and sign == "+")
    return frozenset(answer)


def check_diagrams():
    empty = frozenset()
    a0 = Diagram(frozenset({(0, 0)}), empty, empty, empty)
    a1 = Diagram(a0.forward, empty, empty, frozenset({(0, 1)}))
    b = Diagram(frozenset({(1, 0)}), empty, frozenset({(0, 0)}), empty)
    assert a0.forward == a1.forward and a0.backward == a1.backward
    assert multiply(a0, b, 2).forward == joined_forward(a0, b) == empty
    assert multiply(a1, b, 2).forward == joined_forward(a1, b) == frozenset({(0, 0)})
    # Exhaust all m=1 diagrams as a consistency check on the product code.
    relations = (empty, frozenset({(0, 0)}))
    diagrams = [Diagram(*r) for r in product(relations, repeat=4)]
    for a, b, c in product(diagrams, repeat=3):
        assert multiply(multiply(a, b, 1), c, 1) == multiply(a, multiply(b, c, 1), 1)
    print("two-way: equal through relations; contextual forward-relation sizes 0 and 1")
    print("two-way: all 4096 triples of one-label diagrams satisfy associativity")


def replay(x, y, dirty, op):
    """Four reversible sweeps, two output reads; mute source edges by zeroing x."""
    z = list(dirty)

    def sweep(inputs, reverse=False):
        order = (1, 0) if reverse else (0, 1)
        for gate in order:
            value = op(inputs[0], inputs[1]) if gate == 0 else op(z[0], inputs[2])
            z[gate] ^= value

    sweep(x)
    y ^= z[1]
    sweep(x, reverse=True)
    sweep((0, 0, 0))
    y ^= z[1]
    sweep((0, 0, 0), reverse=True)
    assert tuple(z) == dirty
    return y


def check_replay():
    xor = lambda a, b: a ^ b
    conjunction = lambda a, b: a & b
    xor_good = 0
    and_bad = 0
    for bits in product((0, 1), repeat=6):
        x, y, dirty = bits[:3], bits[3], bits[4:]
        assert replay(x, y, dirty, xor) == y ^ x[0] ^ x[1] ^ x[2]
        xor_good += 1
        actual = replay(x, y, dirty, conjunction)
        expected = y ^ (x[0] & x[1] & x[2])
        assert actual ^ expected == dirty[0] & x[2]
        and_bad += actual != expected
    assert replay((0, 0, 1), 0, (1, 0), conjunction) == 1
    assert (xor_good, and_bad) == (64, 16)
    print("dirty replay: XOR correct on all 64 assignments; scratch always restored")
    print("dirty replay: AND wrong on 16 of 64 assignments, exactly when z0*x2=1")
    print("AND witness: x=(0,0,1), y=0, dirty=(1,0); obtained 1, required 0")


if __name__ == "__main__":
    check_diagrams()
    check_replay()
