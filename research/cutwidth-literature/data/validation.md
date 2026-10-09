# Validation status

[Review home](../index.md) · [Audit runner](audit.py)

All scripts use Python's standard library. They validate arithmetic and finite
examples; they do not certify an improved universal cutwidth constant.

| Artifact | What it checks | Limit |
| --- | --- | --- |
| [Classical](../classical/data/check_classical_deductions.py) / [output](../classical/data/check_classical_deductions.txt) | Current constant; degree-four potential obstruction; anchored-completion floor; cubic specialization of density bounds | Arithmetic consequences of the cited theorems, not new general layout algorithms |
| [Spectral](../spectral/data/check_proposals.py) / [output](../spectral/data/check_proposals-output.json) | Target correlation and entropy arithmetic; 1,088 Boolean assignments for exact median charging; 15,360 threshold instances on 640 small patch graphs | No proof of a uniform positive Gaussian patch gain |
| [Parameters](../parameters/data/validate_conversions.py) / [output](../parameters/data/validation-output.txt) | Independent subset-DP width examples; 729 multigraph tripartitions; common-order counterexample; actual binary code states and transitions | Finite examples and convention checks, not a semantic supply theorem |
| [Reductions](../structural/data/check_reductions.py) / [output](../structural/data/check_reductions.txt) | All local triangle port patterns; 46,472 lifted orders/expansion choices including parallel edges; triangle-density and naive deletion budgets | Supports the paper lifting argument, not a high-girth reduction for all short cycles |
| [Corpus](check_corpus.py) | Unique source anchors, defined consistent citation keys, existing local links, reachable Markdown | Does not verify external claims or URL content |

The deterministic patch and triangle statements also have written arguments in
[patches.md](../spectral/patches.md) and [reductions.md](../structural/reductions.md).
Those arguments were reviewed separately from their finite examples. They were not
added to the Lean formalization. Since production Lean and paper files were unchanged,
this review did not rerun the full repository build or claim a fresh axiom audit.

The source audit uses author/publisher texts and records whether each result was
read in a full relevant section, screened in an abstract, or identified through a
later primary paper. A source's existence is not a proof of its applicability.

## Review and revisions

Three whole-corpus passes covered accuracy, completeness/coherence with a graph-layout
researcher's lens, and source quality/staleness. Each read the data artifacts and
reran the audit. Fresh source checks concentrated on the statements carrying the
application; they did not independently re-prove every publication.

The first iteration found and addressed:

- An integer-rounding error in the recursive-bisection discussion: the safe
  recurrence uses `ceil(m/2)` and yields `2bn+O(log n)`. The leading coefficient
  and the applicability conclusion are unchanged.
- Missing coverage of Cheeger-type spectral sweeps, metric SDP, reweighted vertex
  expansion, and the direct cutwidth SDP in Bansal–Katzelnick–Schwartz Section 6.3.
  The [focused note](../spectral/separators.md) now states the exact missing transfers.
- A complementary Gaussian-wave percolation trail, with the distinction between
  vertex superlevels, median-key bands, and arbitrary-graph component control.
- Separator-balance and Laplacian-normalization conventions, cross-links between
  conversion arguments, final HHKL journal coordinates, and a stale bibliography
  pointer to the Gaussian derivation.

The nested-patch proof, Gaussian threshold profile, simultaneous triangle-lifting
proof, and width/code conversions received mathematical scrutiny separately from
the finite tests. No universal positive gain was established by these checks.

The post-revision accuracy review found no remaining Error, Gap, or Polish finding
within its scope. It checked the six added references, the direct cutwidth SDP,
and the exact exterior-port recurrence, and reran the full corpus audit. Unchanged
material retained the earlier detailed review; this was not a second independent
proof reconstruction of all 68 papers.

The final adversarial audit used a separate model and fresh primary-source fetches.
It found no Error, Gap, or Polish finding within its checked scope. It verified the
six added references, Bansal's direct SDP, selected recent results, principal
conversion constants and numerical directions, and all data artifacts. The port
recurrence and the written patch/triangle arguments were checked separately from
the saved computations.

This final pass did not freshly verify every identifier or every proof across all
68 references. Some metadata endpoints were rate-limited; failed requests were
not treated as evidence. No external numerical optimization was independently
interval-certified, and no Lean rebuild was performed. The literature review
converged with no unresolved findings from these passes, subject to these limits
and the [coverage limitations](../index.md#known-limitations).
