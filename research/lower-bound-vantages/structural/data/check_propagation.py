#!/usr/bin/env python3
# Validates: fixing a gate's inputs leaves exactly its correct output unit.
from itertools import product
checked = 0
for k in range(3):
    rows = list(product((0, 1), repeat=k))
    for values in product((0, 1), repeat=len(rows)):
        clauses = [list(zip(range(k + 1), [1-b for b in row] + [v]))
                   for row, v in zip(rows, values)]
        for row, v in zip(rows, values):
            remaining = [[lit for lit in c if lit[0] == k] for c in clauses
                         if not any(i < k and row[i] == b for i, b in c)]
            assert remaining == [[(k, v)]]
            checked += 1
assert checked == 74
print("Gate propagation: all 74 truth-table/input pairs passed.")
