# Cutwidth literature and routes to stronger frontier bounds

Research review completed 2026-10-09. Baseline checkout: `5c764e808af996822575911f28df7f4c519fc963`.

Start with [the application and priorities](synthesis.md). This review covers 68
distinct references, with source-by-source access depth. It finds no verified
ready-to-use theorem that improves the project's universal cubic coefficient.
The strongest next direction is **bounded-patch optimization with nested minimum
cuts**, combined with a certified uniform gain estimate. The review also derives
a triangle-packing saving, identifies the classical bisection-completion bottleneck,
and checks the costs of switching to tree or semantic capacity parameters.

## Question and exact target

Find published results and methods that improve the Frontier Method's supply theorem.
The current cubic theorem gives, for every fixed positive slack and all sufficiently
large simple cubic graphs on `h` vertices, **one ordering with every prefix cut** at most
`(p + slack) h`, where `p = 3/(2 pi) acos((1 + 2 sqrt(2))/4)`.
Compression gives `A = 2p` relative to cycle rank for loopless subcubic multigraphs,
and the binary circuit coefficient is `L = 1 + 1/A`.

A useful result must control arbitrary graphs, all prefixes of a single order,
parallel edges after restoration, and the appropriate additive error. Bisection,
random-graph, large-girth, single-separator, or separate-order results require
additional transfer arguments. A change in semantic capacity can bypass wire
cutwidth, but needs a universal capacity supply theorem of its own.

## Contents

1. [Classical cutwidth and extremal layout bounds](classical/index.md): historical
   bounds, cubic/subcubic graphs, bisection, pathwidth, exact/approximation algorithms,
   and whether any known all-graph coefficient beats the baseline.
2. [Spectral and probabilistic methods](spectral/index.md): Gaussian waves, factors
   of IID, nonlinear local improvement, percolation, concentration, and barriers
   from expanders and local algorithms; [spectral separators and global SDP](spectral/separators.md)
   covers Cheeger-type sweeps, metric rounding, and reweighted vertex expansion.
3. [Structural and separator methods](structural/index.md): short cycles versus
   high girth, separators, recursive layouts, degree-sensitive reductions, and
   cycle-rank accounting.
4. [Related parameters and capacity](parameters/index.md): linear branchwidth,
   carving width, line-graph widths, rankwidth, matroid pathwidth, hypergraph cuts,
   tree decompositions, and complete-transition capacity.
5. [Application and research priorities](synthesis.md): exact compatibility map,
   quantitative targets, proved deductions, candidate improvements, and missing lemmas.

Ownership boundaries: classical covers extremal theorems and algorithms; spectral
covers random/local/spectral constructions and their expansion obstructions;
structural covers deterministic transformations and restoration costs; parameters
covers width and capacity conversions. Lower-bound examples must be checked as
carefully as proposed upper bounds. Vertex orders, edge orders, decomposition trees,
and semantic state orders are distinct objects until a conversion is proved.

The `5n` circuit target requires `p = 1/8` and `A = 1/4` (up to vanishing slack).
This is a substantive reduction from the baseline, not an additive-error improvement.

The [bibliography](sources.md) records access depth and limitations. Search coverage
is recorded in [the search log](data/search-log.md). Detailed deductions are in
[the patch note](spectral/patches.md) and [the short-cycle note](structural/reductions.md);
[the algorithmic companion](classical/algorithms.md) explains which tools are useful
for experiments.

## Open questions for the review

- Is there a published universal cubic cutwidth bound below `p h`?
- Can local improvements supply a uniform positive gain near the worst threshold,
  including graphs with many short cycles?
- Can a short-cycle reduction pay for itself in the same width budget as a high-girth gain?
- Do spectral, SDP, or separator profiles give a coherent all-prefix layout?
- Can a related connectivity parameter reduce the cost of complete transitions,
  without losing the saving during conversion or choosing incompatible orders?

## Supplementary Code

Run `python3 research/cutwidth-literature/data/audit.py` from the repository root.
It reruns the following checks and compares their output with saved results:

- [Classical reduction arithmetic](classical/data/check_classical_deductions.py).
- [Gaussian arithmetic, median-charge identity, and nested patch examples](spectral/data/check_proposals.py).
- [Width conversions, joint boundaries, and complete code transitions](parameters/data/validate_conversions.py).
- [Triangle lifting and restoration budgets](structural/data/check_reductions.py).
- [Citation and local-link consistency](data/check_corpus.py).

The [validation record](data/validation.md) distinguishes finite checks from the
paper deductions and from the missing universal gain theorem.

## Known Limitations

This is a broad, targeted literature review, not a certification that every historical
paper has been found or read. Search-index coverage, inaccessible full texts, and
unpublished work limit completeness. Mathematical proposals are labeled separately
from published theorems and checked repository results.

No production Lean or manuscript theorem was changed. The paper deductions in this
corpus have not been formalized. Earlier project high-girth certificates were not
recoverable at their recorded temporary paths and were not revalidated here.
