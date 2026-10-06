#!/usr/bin/env python3
"""Validates: XOR-AND normal form, affine normality, and three failed transfers.

The general normality theorem is proved in ../index.md and credited there to
the existing multiplicative-complexity literature. These are finite checks,
not a new asymptotic circuit lower bound. Run from any working directory.
"""

from fractions import Fraction
from itertools import product
from random import Random


def coefficients(table):
    c = table & 1
    a = ((table >> 2) & 1) ^ c
    b = ((table >> 1) & 1) ^ c
    q = sum((table >> j) & 1 for j in range(4)) % 2
    return c, a, b, q


def truth(table, a, b):
    return (table >> (2 * a + b)) & 1


def affine_value(form, assignment):
    mask, c = form
    return (mask & assignment).bit_count() % 2 ^ c


def add_forms(left, right):
    return left[0] ^ right[0], left[1] ^ right[1]


def shifted(form, c):
    return form[0], form[1] ^ c


def normal_form(n, circuit):
    wires = [(1 << j, 0) for j in range(n)]
    equations = []
    for left, right, table in circuit:
        c, a, b, q = coefficients(table)
        u, v = wires[left], wires[right]
        if q:
            equations.append((shifted(u, b), shifted(v, a)))
            wires.append((1 << (n + len(equations) - 1), c ^ (a & b)))
        else:
            wires.append(add_forms((u[0] * a, u[1] * a),
                                   shifted((v[0] * b, v[1] * b), c)))
    return equations, wires[-1]


def direct_values(n, circuit, x):
    values = [(x >> j) & 1 for j in range(n)]
    for left, right, table in circuit:
        values.append(truth(table, values[left], values[right]))
    return values


def is_affine_space(points):
    base = min(points)
    differences = {x ^ base for x in points}
    return all(a ^ b in differences for a in differences for b in differences)


def normality_certificate(n, circuit):
    # Use evaluated truth tables, independently of symbolic normal_form.
    values = [direct_values(n, circuit, x) for x in range(1 << n)]
    points = set(range(1 << n))
    for j, (left, right, table) in enumerate(circuit):
        if coefficients(table)[3]:
            left_values = {values[x][left] for x in points}
            if len(left_values) == 2:
                points = {x for x in points if values[x][left] == 0}
            # The gate is now affine; later gates retain its defining equation.
            assert is_affine_space(points)
        # Every processed wire must be affine on the current affine space.
        base = min(points)
        for a in points:
            for b in points:
                c = a ^ b ^ base
                assert values[c][n + j] == (
                    values[a][n + j] ^ values[b][n + j] ^ values[base][n + j]
                )
    if len({values[x][-1] for x in points}) == 2:
        points = {x for x in points if values[x][-1] == 0}
    assert points and is_affine_space(points)
    assert len({values[x][-1] for x in points}) == 1
    k = sum(coefficients(table)[3] for _, _, table in circuit)
    assert len(points) >= 1 << max(0, n - k - 1)
    return len(points)


def rank(matrix):
    work = [[Fraction(x) for x in row] for row in matrix]
    r = 0
    for c in range(len(work[0])):
        pivot = next((i for i in range(r, len(work)) if work[i][c]), None)
        if pivot is None:
            continue
        work[r], work[pivot] = work[pivot], work[r]
        value = work[r][c]
        work[r] = [x / value for x in work[r]]
        for i in range(len(work)):
            if i != r:
                value = work[i][c]
                work[i] = [x - value * y for x, y in zip(work[i], work[r])]
        r += 1
    return r


def main():
    for table, a, b in product(range(16), range(2), range(2)):
        c, alpha, beta, q = coefficients(table)
        assert truth(table, a, b) == c ^ (alpha & a) ^ (beta & b) ^ (q & a & b)
        if q:
            assert truth(table, a, b) == ((a ^ beta) & (b ^ alpha)) ^ c ^ (alpha & beta)
    print("Binary normalization: 16 truth tables, 64 evaluations passed.")

    rng = Random(20261006)
    checked_inputs = 0
    for trial in range(240):
        n = 2 + trial % 5
        circuit = [(rng.randrange(n + j), rng.randrange(n + j), rng.randrange(16))
                   for j in range(1 + trial % 10)]
        equations, output = normal_form(n, circuit)
        for x in range(1 << n):
            assignment = x
            for j, (u, v) in enumerate(equations):
                z = affine_value(u, assignment) & affine_value(v, assignment)
                assignment |= z << (n + j)
            assert affine_value(output, assignment) == direct_values(n, circuit, x)[-1]
            checked_inputs += 1
        normality_certificate(n, circuit)
    print(f"Normal form and monochromatic-flat certificates: 240 circuits, {checked_inputs} inputs passed.")

    n = 6
    outputs = [x.bit_count() % 2 for x in range(1 << n)]
    # Multilinear interpolation over the reals and over F_2 use the same cube.
    real_coefficients = outputs[:]
    binary_coefficients = outputs[:]
    for j in range(n):
        for x in range(1 << n):
            if (x >> j) & 1:
                real_coefficients[x] -= real_coefficients[x ^ (1 << j)]
                binary_coefficients[x] ^= binary_coefficients[x ^ (1 << j)]
    assert max(x.bit_count() for x, c in enumerate(real_coefficients) if c) == n
    assert max(x.bit_count() for x, c in enumerate(binary_coefficients) if c) == 1
    print("Affine pullback counterexample: projection degree 1 becomes real degree 6; F_2 degree remains 1.")

    rows = list(product(range(2), repeat=4))
    assert len(set(rows)) == 16 and rank(rows) == 4
    print("Index-function counterexample: 16 distinct Boolean residuals have rational span dimension 4.")

    # Coefficient flattening of product_i (x_i + y_i): complementary subsets.
    flattening = [[int(a ^ b == 15) for b in range(16)] for a in range(16)]
    assert rank(flattening) == 16
    print("Partition-rank counterexample: a 7-gate arithmetic formula has coefficient rank 16.")

    a = b = 1
    assert a + b - 2 * a * b == a ^ b == 0
    assert bool(a or b or a * b)
    print("Cancellation counterexample: XOR is zero at (1,1), while union of arithmetic term supports accepts.")


if __name__ == "__main__":
    main()
