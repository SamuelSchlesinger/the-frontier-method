# Validation record

[Corpus](../index.md) · [Aggregate validator](validate.py)

Executed 2026-10-06 with Python 3 and the standard library. Each expected-output
file is retained for reproducibility. These are finite checks of implementations,
examples, and numerical accounting, not proofs of the missing universal theorems.

| Check | Recorded output | Scope |
|---|---|---|
| [Layout identity](check_layout_identity.py) | [JSON](layout-output.json) | All 1,099 labeled simple graphs on one through five vertices, plus named examples; independent join and elimination recurrences; nonlinear support counterexample |
| [Combinatorial transfers](../combinatorial/data/check_claims.py) | [Text](../combinatorial/data/expected.txt) | Gate classification, 29,511 parity restrictions, INDEX cofactors, 7,200 product-fiber rectangles, surplus arithmetic, weighted-elimination branching factors |
| [Semantic quotients](../communication/data/check_semantic_quotients.py) | [Text](../communication/data/expected.txt) | Exhaustive 256 interlayer relations for the three-bit example; counts before and after both quotient operations |
| [Algebraic transfers](../algebraic/data/check_bridges.py) | [Text](../algebraic/data/expected.txt) | All binary gates, 240 generated circuits and 5,952 inputs, normality certificates, degree/rank/cancellation examples |
| [Gate propagation](../structural/data/check_propagation.py) | [Text](../structural/data/expected.txt) | All 74 truth-table/input cases of arity zero, one, and two |

The aggregate validator re-executes all five checks and compares their full output.
It also checks citation definitions, canonical display keys, unused source
anchors, relative links, and reachability of every Markdown document from the
corpus index. It excludes code spans and fenced examples from citation parsing.

External source checking and mathematical review are separate from this mechanical
gate. The bibliography identifies the primary sources and versions. The new
deductions were reviewed as paper arguments; no new Lean declarations or proofs
were added by this comparison.
