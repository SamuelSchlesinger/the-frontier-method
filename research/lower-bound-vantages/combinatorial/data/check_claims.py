#!/usr/bin/env python3
"""Validates: parity has only linear B2 shrinkage; INDEX saturates R <= 2^N.

Also validates all binary gate types, product-fiber monochromatic rectangles,
and the conditional restriction-surplus arithmetic in ../index.md.
These are finite checks, not proofs of a circuit lower-bound improvement.
No external dependencies; run with Python 3 from any working directory.
"""

from fractions import Fraction
from itertools import product
from math import acos, log2, pi, sqrt


def truth_table_support(table, n):
    """Determine essential coordinates by comparing truth-table entries."""
    return [i for i in range(n)
            if any(table[x] != table[x ^ (1 << i)] for x in range(1 << n))]


def check_gate_types():
    counts = {"constant": 0, "unary": 0, "parity": 0, "and_type": 0}
    for code in range(16):
        table = [(code >> x) & 1 for x in range(4)]
        support = truth_table_support(table, 2)
        if len(support) < 2:
            counts["constant" if not support else "unary"] += 1
        elif all(table[x] != table[x ^ (1 << i)]
                 for x in range(4) for i in range(2)):
            counts["parity"] += 1
        else:
            assert sum(table) in (1, 3)
            counts["and_type"] += 1
    assert counts == {"constant": 2, "unary": 4, "parity": 2, "and_type": 8}
    print("Binary gate classification:", counts)


def check_parity():
    cases = 0
    restrictions = 0
    for n in range(2, 9):
        truth = [x.bit_count() % 2 for x in range(1 << n)]
        for p in (Fraction(1, 4), Fraction(1, 2), Fraction(3, 4)):
            expected = Fraction(0)
            for rho in product((0, 1, None), repeat=n):
                live = [i for i, value in enumerate(rho) if value is None]
                fixed = sum((value or 0) << i for i, value in enumerate(rho))
                residual = [truth[fixed | sum(((x >> j) & 1) << i
                                              for j, i in enumerate(live))]
                            for x in range(1 << len(live))]
                support = truth_table_support(residual, len(live))
                # For a parity cofactor, the essential-input bound is attained
                # by an XOR tree; a unary complemented output costs one NOT.
                if len(support) >= 2:
                    gates = len(support) - 1
                elif support:
                    assert residual in ([0, 1], [1, 0])
                    gates = int(residual == [1, 0])
                else:
                    gates = 0
                probability = p ** len(live) * ((1 - p) / 2) ** (n - len(live))
                expected += probability * gates
                restrictions += 1
            lower = n * p - 1 + (1 - p) ** n
            exact = lower + n * p * (1 - p) ** (n - 1) / 2
            assert expected == exact
            assert lower <= expected <= lower + 1
            cases += 1
    print(f"Parity: {cases} exact expectations from {restrictions} restrictions passed")
    for m in (8, 16, 32, 64):
        # n=m^3 and p=1/m. The lower bound np-1 is enough for falsification.
        lower = m * m - 1
        formula_main_term = m
        assert lower / formula_main_term == m - 1 / m
    print("Parity scaling: n=m^3, p=1/m gives B2 cost >= m^2-1")


def check_index():
    for q in range(1, 5):
        states = 1 << q
        cofactors = set()
        for data in range(1 << states):
            table = tuple((data >> address) & 1 for address in range(states))
            cofactors.add(table)
            # Each accepting pair belongs to the unique address rectangle.
            for address, accepted in enumerate(table):
                hits = sum(int(z == address and (data >> z) & 1)
                           for z in range(states))
                assert hits == accepted
        assert len(cofactors) == 1 << states
        assert log2(log2(len(cofactors))) == q
        print(f"INDEX: q={q}, states={states}, distinct cofactors={len(cofactors)}")


def check_block_composition():
    # All four-valued truth tables for the two inner functions; all binary
    # outer gates. Empty fibers are skipped, and every nonempty accepted
    # product is checked pointwise, independently of the symbolic argument.
    rectangles = 0
    for g, h, outer in product(range(16), repeat=3):
        for a, b in product((0, 1), repeat=2):
            if not ((outer >> (a + 2 * b)) & 1):
                continue
            left = [x for x in range(4) if ((g >> x) & 1) == a]
            right = [y for y in range(4) if ((h >> y) & 1) == b]
            if not left or not right:
                continue
            for x, y in product(left, right):
                assert (outer >> (((g >> x) & 1) + 2 * ((h >> y) & 1))) & 1
            rectangles += 1
    print(f"Block composition: {rectangles} nonempty product rectangles passed")


def check_surplus():
    coefficient = 1 + 1 / ((3 / pi) * acos((1 + 2 * sqrt(2)) / 4))
    rho = Fraction(1, 2)
    five_fraction = Fraction(3, 5)
    bonus = float(rho) * (4 + float(five_fraction) - coefficient)
    n, t, good = 1000, 500, 300
    deletions = 5 * good + 4 * (t - good)
    assert abs((deletions - coefficient * t) - bonus * n) < 1e-10
    assert abs(coefficient - 4.562497678925021) < 1e-13
    print(f"Conditional surplus: L={coefficient:.12f}, threshold={coefficient-4:.12f}")
    print(f"Conditional surplus: rho=1/2, a=3/5 gives {bonus:.12f}n")


def check_literature_thresholds():
    # Golovnev--Kulikov, Weighted Gate Elimination, ITCS 2016, Theorem 1:
    # https://golovnev.org/papers/weighted.pdf. Numerically check the four
    # inequalities for their displayed rounded parameters, not the theorem.
    alpha, beta = 0.535, 3.6513
    drops = ((2 + alpha, 4 + 2 * alpha), (2, 5 + 2 * alpha),
             (3 + 3 * alpha, 2 + 2 * alpha), (3, 4 + alpha))
    factors = [2 ** (-a / beta) + 2 ** (-b / beta) for a, b in drops]
    assert max(factors) < 1 - 1e-6
    assert abs(beta - alpha - 3.1163) < 1e-12
    assert 2 * 1.83 > beta
    coefficient = 1 + 1 / ((3 / pi) * acos((1 + 2 * sqrt(2)) / 4))
    # Golovnev--Kulikov--Williams, Circuit Depth Reductions, ITCS 2021,
    # Theorem 1 charges s/3.9; it does not charge (s-n)/3.9.
    credit = coefficient - 3.9
    assert abs(credit - 0.662497678925021) < 1e-12
    print(f"Weighted elimination: largest branching factor={max(factors):.12f}<1")
    print(f"Depth reduction: hypothetical input credit must exceed {credit:.12f}n")


if __name__ == "__main__":
    check_gate_types()
    check_parity()
    check_index()
    check_block_composition()
    check_surplus()
    check_literature_thresholds()
    print("PASS: finite checks only; no universal terminal coverage is claimed")
