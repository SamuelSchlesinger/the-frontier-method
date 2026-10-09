# Coverage and search limitations

[Review home](../index.md) · [Master sources](../sources.md)

Review date: 2026-10-09. The initial graph theorem and proof architecture were
checked in repository commit `5c764e808af996822575911f28df7f4c519fc963`.
The deliverable is a targeted source audit and application analysis. It is not a
claim to have read every paper containing the word cutwidth.

| Lane | Vocabulary / trail | Detailed record |
| --- | --- | --- |
| Classical | cutwidth, cut linear arrangement, cubic/subcubic, pathwidth, vertex separation, bisection, density lower bounds, exact/approximation algorithms; Díaz–Petit–Serna and Petit survey trails | [Classical log](../classical/data/search-log.md) |
| Spectral/probabilistic | Gaussian wave, factors of IID, local improvement, min bisection, max cut, spectral rounding, SDP, entropy, parametric cuts, coarea | [Spectral log](../spectral/data/search-log.md) |
| Structural | separator profiles, excluded minors, pair crossing number, short cycles, triangle contraction, degree-sensitive reduction | [Structural log](../structural/data/search-log.md) |
| Parameters/capacity | searching, linear-width, carving/branchwidth, line graphs, rankwidth, matroid pathwidth, trellis complexity, hypergraphs, symmetric submodularity | [Parameter log](../parameters/data/search-log.md) |

The root search additionally used `cutwidth cubic graphs upper bound 2024 2025 2026`,
`cutwidth cubic graphs 1/6 Monien Preis pathwidth Fomin Hoie`, `cutwidth spectral bounds
Laplacian`, `cutwidth semidefinite Gaar 2024`, and numeric cubic cutwidth/pathwidth
queries for `0.14` and `0.13`. Primary records and author/publisher full texts were
preferred over search snippets and third-party summaries. Search-result crawl dates
were not treated as publication dates.

Backward references from load-bearing papers and targeted searches for later work
were used. This is not a full citation-graph crawl. Current sources include 2025–2026
papers and preprints; their publication status and version matter. Where only a
primary abstract or record was accessible, the bibliography says so. A full-text
label means the relevant text was inspected, not that every proof was independently
reproved.

The graph families covered include arbitrary bounded-degree graphs, simple cubic
graphs, loopless multigraphs after restoration, random regular graphs, high-girth
graphs, trees, planar/minor-free/geometric classes, and compiled signal hypergraphs.
Special families are included for methods or restricted results; they do not stand
in for the universal graph class.

Historical local research summaries were consulted to avoid presenting the prior
high-girth/finite-cone work as new. Their temporary certificate files could not be
recovered at the recorded paths, so those claims were not revalidated or promoted.

Unresolved coverage limits: inaccessible historical full texts; no systematic
non-English search; unpublished work; incomplete indexing of the newest preprints;
and no complete bibliometric census of forward citations. These limits prevent an
exhaustiveness or priority certification, while still allowing specific theorem
compatibility and arithmetic checks.
