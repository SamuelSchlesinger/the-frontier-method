#!/usr/bin/env python3
"""Validates: local upper certificates can be mixed only on common refinements.

The finite rational check exercises the pointwise-minimum inequality formalized
in Frontier/Boundary/Communication.lean. It also gives an independent example
showing why per-cut message counts cannot be multiplied as independent signals.
These checks do not prove a universal circuit capacity improvement.
"""

from fractions import Fraction
from itertools import product
import json


def main():
    checked = 0
    # Child square-root masses 3/5 and 4/5 come from probabilities 9/25,16/25.
    weights = (Fraction(3, 5), Fraction(4, 5))
    strict = 0
    for a, b, c, d in product(range(1, 6), repeat=4):
        left, right = (a, b), (c, d)
        v = sum(p * x for p, x in zip(weights, left))
        w = sum(p * x for p, x in zip(weights, right))
        mixed = sum(p * min(x, y) for p, x, y in zip(weights, left, right))
        assert mixed <= min(v, w)
        strict += mixed < min(v, w)
        checked += 1

    # Both messages separately have two values. Their common refinement has
    # four values when they are independent, and two when they coincide.
    independent = {(x, y) for x, y in product((0, 1), repeat=2)}
    shared = {(x, x) for x in (0, 1)}
    assert len(independent) == 4 and len(shared) == 2

    # The reverse closure is false for upper certificates: different children
    # can choose different maxima. Keep the same actual parent and masses.
    v = (1, 4)
    w = (4, 1)
    parent_max = max(sum(p * x for p, x in zip(weights, v)),
                     sum(p * x for p, x in zip(weights, w)))
    children_max = sum(p * max(x, y) for p, x, y in zip(weights, v, w))
    assert children_max > parent_max
    print(json.dumps({
        "minimum_certificate_checks": checked,
        "strict_local_retightenings": strict,
        "max_counterexample": {
            "parent": str(parent_max), "children": str(children_max)},
        "joint_message_counts": {"independent": len(independent), "shared": len(shared)},
        "scope": "finite checks; no universal root budget"
    }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
