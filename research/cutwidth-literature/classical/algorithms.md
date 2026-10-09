# Algorithms as a tool for improving the theorem

Back to [classical bounds](index.md). These results compute or approximate
the optimum of an input graph; none supplies a better universal cubic
coefficient by itself. A returned complete vertex order is directly checkable.

## Exact computation and finite interfaces

Bodlaender–Fomin–Koster–Kratsch–Thilikos Theorems 1, 3, and 10 give
`O*(2^n)` time and space, or `O*(4^n)` time with polynomial space, for
cutwidth and several other vertex-ordering problems. Theorem 1's subset
dynamic program specializes to
`F(S)=max{|delta_G(S)|, min_{v in S}F(S\{v})}`, with `F(empty)=0`.
Storing a predecessor recovers a witnessing order. The boundary is measured
in the original graph, not merely in `G[S]`. This is a suitable independent
oracle for small examples. [bodlaender12][bodlaender12]

Thilikos–Serna–Bodlaender's *Cutwidth I* decides width at most a fixed `k`
and returns a layout in linear time in `n`; the hidden dependence is on `k`.
*Cutwidth II* treats bounded-degree partial `w`-trees with an
`n^{O(w^2 d)}` bound and recovers optimal orders. These are computational
tools for already small widths or treewidth, not proofs that arbitrary
cubic graphs have such width. Publisher abstracts were checked.
[thilikos05a][thilikos05a] [thilikos05b][thilikos05b]

Giannopoulou et al. prove that minimal immersion obstructions to cutwidth
at most `k` have at most `2^{O(k^3 log k)}` vertices and edges (Theorem 1
of the full preprint). Their Theorem 2 gives a
`2^{O(k^2 log k)} n` decision-and-layout algorithm.
The proof uses linked orders and finite boundary interfaces; these can inspire
local gadget replacement criteria. [giannopoulou19][giannopoulou19]

The obstruction bound does not turn the desired asymptotic coefficient into
a finite search: here `k` grows with `n`. A useful finite certificate would
instead require a proved local reduction system with a decreasing potential
and a complete set of irreducible cases. That is a new theorem obligation.

## Recent approximation results: useful coherent orders, large losses

Bansal–Katzelnick–Schwartz Theorem 1 gives an efficient
`O(log(n) exp(O(sqrt(log log n))))` approximation for cutwidth.
Their Theorem 2 obtains cutwidth and minimum-linear-arrangement guarantees
in the same order. Section 3 constructs an ordered metric partition and
recurses on its parts, addressing simultaneous cuts directly.
[bansal24][bansal24]

This is conceptually relevant to all-prefix consistency. Its approximation
factor still grows with `n`, so applying it to a graph whose optimal width
is linear gives no coefficient improvement over the repository bound.
A useful adaptation would need to exploit subcubic structure to replace
the accumulated metric-decomposition loss by a controlled constant.

Their Section 6.3 also proposes a direct SDP carrying a cut metric for every
pivot. The [global spectral/SDP note](../spectral/separators.md) explains this
more specific rounding research target and the missing all-prefix guarantee.

Bentert–Fomin–Inamdar–Saurabh Proposition 4 gives a factor-two approximation
for directed cutwidth in `O*(2^{omega n/3})` time, where `omega` is the
matrix-multiplication exponent. Their directed objective counts backward
arcs; the undirected problem embeds by replacing each edge with opposite
arcs, so each crossing edge contributes once. This is a faster exponential
benchmark, not the approximation scheme they obtain for feedback arc set.
Proposition 11 handles the weighted version with factor `2+epsilon`.
[bentert25][bentert25]

## Direct cutwidth SDP: both bounds, but check sparse performance

Gaar–Puges–Wiegele formulate cutwidth through linear-ordering variables,
relax to an SDP, and strengthen it with 3-dicycle equations, triangle
inequalities, and inequalities from ordering polytopes (Section 2).
Algorithm 2 computes lower bounds; Section 3.2 constructs feasible orders
and improves their widths using simulated annealing. [gaar24][gaar24]

Their Section 4.3.1 explicitly reports that the SDP approach is not
competitive with MILP approaches on very sparse benchmark graphs.
For cubic graphs it should therefore be tested against exact subset DP or
ILP, rather than assumed to be the strongest practical oracle.
The paper links code and instances as arXiv ancillary files; they were
identified but not executed in this review. [gaar24][gaar24]

An SDP optimum is a lower bound, and its rounded order supplies an upper
bound. They have different evidentiary roles. A feasible order needs only
integer recounting to verify; turning floating-point dual output into a
rigorous lower-bound certificate requires a separate validation step.
No finite optimization result proves an all-graph asymptotic constant.

## A focused experimental program

Start with small cubic cores, including graphs with many triangles, small
edge cuts, and expansion-oriented examples. Compare the existing Gaussian
order with exact subset DP, then test local vertex moves or block changes
using the maximum over every prefix as the objective. Record graph data,
the complete order, all prefix boundaries, and the independent lower bound.

For a proposed reduction, test all relevant boundary attachment patterns,
not only the isolated gadget's optimum. The live frontier outside a gadget
can change which local order is safe. A successful finite experiment should
be distilled into a boundary-aware lemma and charged against cycle rank.
See [structural restoration](../structural/index.md) for this accounting.

## Known limitations

This companion screens computational methods for their research role.
It does not reproduce implementations or benchmarks, audit numerical SDP
certificates, or claim that older runtime bounds are still optimal in 2026.
Special-family algorithms and metaheuristics are navigable through the
historical surveys and recent papers' references, but were not all read.

[bansal24]: ../sources.md#bansal24
[bentert25]: ../sources.md#bentert25
[bodlaender12]: ../sources.md#bodlaender12
[gaar24]: ../sources.md#gaar24
[giannopoulou19]: ../sources.md#giannopoulou19
[thilikos05a]: ../sources.md#thilikos05a
[thilikos05b]: ../sources.md#thilikos05b
