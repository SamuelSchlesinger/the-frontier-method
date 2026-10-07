#!/usr/bin/env python3
"""Validates: common-output moment scaling and output-conditioning counterexamples.

The distributions below are enumerated from independent fair input bits using
integer counts. Analytic formulas are checked against that enumeration. Floating
point entropy comparisons are consistency checks, not proofs of any upstream
theorem or a universal circuit coefficient. The proofs are in ../index.md.
Run from the repository root: python3 research/openai-math/capacity/data/check_transfer.py
"""

from collections import Counter
from itertools import product
from math import acos, fsum, isclose, log2, pi, sqrt


def distribution(counts):
    total = sum(counts.values())
    return {key: count / total for key, count in counts.items() if count}


def moment(p, theta):
    return fsum(mass**theta for mass in p.values())


def entropy(p, theta=1.0):
    if theta == 1.0:
        return -fsum(mass * log2(mass) for mass in p.values())
    return log2(moment(p, theta)) / (1 - theta)


def close(a, b):
    assert isclose(a, b, rel_tol=2e-12, abs_tol=2e-12), (a, b)


def selector_counts(k):
    """Y_i = selector AND input_i; retain selector and output parity too."""
    ys, tagged, outputs = Counter(), Counter(), {0: Counter(), 1: Counter()}
    for selector, *xs in product((0, 1), repeat=k + 1):
        y = tuple(selector & x for x in xs)
        output = sum(y) % 2
        ys[y] += 1
        tagged[(selector, y)] += 1
        outputs[output][y] += 1
    return ys, tagged, outputs


def run():
    theta_values = (0.25, 0.5, 0.75, 0.9)
    linear_failures = 0
    for theta, lam in product(theta_values, (0.25, 0.5, 0.75)):
        # The common output and active core are each deterministic but distinct.
        p = {0: 1 - lam, 1: lam}
        exact_flag_charge = (1 - lam) ** theta + lam**theta
        close(moment(p, theta), exact_flag_charge)
        assert moment(p, theta) > (1 - lam) * 1 + lam * 1
        linear_failures += 1
    print(f"Rejected linear moment-thinning inequalities: {linear_failures}")

    comparisons = 0
    for k in (2, 4, 8, 12):
        ys, tagged, outputs = selector_counts(k)
        p, pt = distribution(ys), distribution(tagged)
        zero = (0,) * k
        assert ys[zero] == 2**k + 1
        assert all(count == 1 for y, count in ys.items() if y != zero)
        assert sum(outputs[1].values()) == 2 ** (k - 1)
        assert len(outputs[1]) == 2 ** (k - 1)
        assert set(outputs[1].values()) == {1}
        odd = distribution(outputs[1])
        for theta in theta_values:
            closed = (0.5 + 2 ** (-k - 1)) ** theta + (2**k - 1) * 2 ** (-(k + 1) * theta)
            flag = 0.5**theta * (1 + 2 ** ((1 - theta) * k))
            close(moment(p, theta), closed)
            close(moment(pt, theta), flag)
            assert moment(p, theta) <= flag + 2e-12
            close(entropy(odd, theta), k - 1)
            # Class masses remain unconditional in a complete transition bound.
            class_weighted = fsum(
                (sum(counts.values()) / 2 ** (k + 1)) ** theta
                * moment(distribution(counts), theta)
                for counts in outputs.values()
            )
            close(class_weighted, moment(p, theta))
            # A separate fair bit attains the output-refinement factor.
            fair_refinement = {(y, b): mass / 2 for y, mass in p.items() for b in (0, 1)}
            close(moment(fair_refinement, theta), 2 ** (1 - theta) * moment(p, theta))
            comparisons += 1
        if k == 12:
            marginal = {0: 0.75, 1: 0.25}
            hroot, marginal_sum = entropy(p, 0.5), k * entropy(marginal, 0.5)
            assert hroot > marginal_sum
            print(f"k=12: H1(Y)={entropy(p):.8f}; H1/2(Y)={hroot:.8f}")
            print(f"k=12: sum marginal H1/2={marginal_sum:.8f}; H1/2(Y | parity=1)={entropy(odd, 0.5):.8f}")
            print("k=12: Pr[parity=1]=0.25000000; odd-support size=2048")
    print(f"Enumerated selector/moment/output comparisons: {comparisons}")

    # Conditioning on XOR=0 destroys independence of two fair input bits.
    even_pairs = distribution(Counter((u, v) for u, v in product((0, 1), repeat=2) if u ^ v == 0))
    assert even_pairs == {(0, 0): 0.5, (1, 1): 0.5}
    marginal_u = fsum(p for (u, _), p in even_pairs.items() if u == 0)
    marginal_v = fsum(p for (_, v), p in even_pairs.items() if v == 1)
    assert marginal_u * marginal_v == 0.25 and even_pairs.get((0, 1), 0) == 0
    print("Conditioning test: P[01 | XOR=0]=0, product of conditional marginals=1/4")

    a = (3 / pi) * acos((1 + 2 * sqrt(2)) / 4)
    print(f"A={a:.12f}; current 1+1/A={1 + 1/a:.12f}; hypothetical B=1/4 gives 5")
    print("PASS (finite checks only; no upstream proof or universal root budget verified)")


if __name__ == "__main__":
    run()
