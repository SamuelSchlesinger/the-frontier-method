# Classical cutwidth, extremal bounds, and the useful reduction barriers

Back to the [review](../index.md). Review date: 2026-10-09.
The [algorithmic companion](algorithms.md) covers exact computation, approximation,
SDP, and finite obstructions. The [search log](data/search-log.md) records coverage
and access failures; [validation code](data/check_classical_deductions.py) checks
the scalar deductions below, with [expected output](data/check_classical_deductions.txt).

## What this literature changes

No source verified in this classical search supplies a universal cubic cutwidth
coefficient below the repository's `p = 0.1403509686...`.
This is a search outcome, not a proof that no such result exists.
The most actionable findings are two precise obstacles to importing better results:
the Fomin–Høie bisection-to-pathwidth proof has an independent `n/6` floor,
and the Edwards–McDermid degree-reduction potential cannot accept a cubic
coefficient below `1/6` without changing its proof. Both observations concern
particular methods, not barriers to the desired theorem.

There is also a sharper classical conversion `cw(G) <= pw(G)+2` for subcubic
simple graphs. It reduces the additive constant in the paper's present `+4`
conversion, but leaves `A` and the circuit coefficient unchanged. The historical
chain and its access limitations are given below.

## Normalization and direction of implication

Write `cw(G) = min_order max_i |delta(prefix_i)|`; pathwidth is maximum bag
cardinality minus one. Bisection width is the minimum boundary of a set of
size `floor(n/2)`. Consequently `bw(G) <= cw(G)`.
Vertex separation counts prefix vertices with a suffix neighbor, rather than
crossing edges; Kinnersley's equivalence identifies its optimum with pathwidth.
Thus `pw(G) <= cw(G)` is in the lower-bound direction. [kinnersley92][kinnersley92]

The edge-isoperimetric profile `b_G(k) = min_{|S|=k}|delta(S)|` gives
`max_k b_G(k) <= cw(G)`. This inequality alone does not provide nested minimizers.
An upper bound on every `b_G(k)` separately is therefore not an all-prefix
layout theorem. The same warning applies to a catalog of excellent bisections.

For a connected cubic graph, `beta_1 = n/2+1`. A leading bound `cw <= c n+o(n)`
therefore transfers through the repository's compression theorem to `A=2c`,
with `L=1+1/(2c)`. The target `L=5` requires `c=1/8`, not just a smaller
constant additive error. Disconnected components can be concatenated, taking
the maximum of component widths; the cycle ranks, however, add.

## Historical route map

The 2002 survey by Díaz, Petit, and Serna is the principal historical index for
layout definitions, complexity, approximation, and graph families. Its publisher
record was verified; full survey access failed. Petit's 2011 addendum was read
in full and updates algorithms and special classes, but explicitly excludes
new random-graph results and other layout variants. Neither survey is used
as primary evidence for a numerical theorem below. [diaz02][diaz02] [petit11][petit11]

| Verified result | Scope and direction | Relevance to the present coefficient |
| --- | --- | --- |
| Monien–Preis, Theorem 1: `bw <= (1/6+epsilon)n` for sufficiently large simple cubic graphs | One balanced cut; fixed positive slack; constructive local improvement | Historical universal baseline, weaker than `p` and insufficient alone for an order. [monienpreis06][monienpreis06] |
| Fomin–Høie, Theorem 5: `pw <= (1/6+epsilon)n` for sufficiently large simple graphs of maximum degree three | Path decomposition; polynomial construction explained in Section 4 | Genuine all-prefix supply after the subcubic conversion, but coefficient `1/6`. [fominhoie06][fominhoie06] |
| Korach–Solel: `cw = O(tw * Delta * log n)` | General graph conversion; upper bound | Useful when treewidth is much smaller than `n/log n`; no favorable linear constant for arbitrary cubic graphs. [korachsolel93][korachsolel93] |
| Subcubic `pw <= cw <= pw+2` | Ordinary simple graphs, componentwise extension | Makes a better universal cubic pathwidth theorem sufficient, with no multiplicative loss. [makedonsudborough89][makedonsudborough89] [ellis94][ellis94] |
| Edwards–McDermid, Corollary 5.2 | Degree-sensitive pathwidth after series-parallel reductions | A useful reduction template, with a coefficient-range obstruction below. [edwardsmcdermid15][edwardsmcdermid15] |

Monien–Preis improve a balanced partition by moving a helpful small set and then
restoring balance. Their Section 1.3 and Theorem 1 are source-verified, including
the quantifier “for every positive epsilon, sufficiently large.” No exact
`n/6` bound for all finite orders is asserted here. The technique is relevant
to local repair, but simultaneous repair of all thresholds is an additional
requirement. [monienpreis06][monienpreis06]

## Why a better bisection alone does not fix the classical bridge

Fomin–Høie Lemma 4 gives a path decomposition of a subcubic graph on `N` vertices
ending at a prescribed set `X`, of width at most
`max{|X|, floor(N/3)+1} + (2/3)log_3 N + 1`.
Their Theorem 5 applies this to the two halves of a bisection and joins the
boundary bags. Full published text, including this proof, was read.
[fominhoie06][fominhoie06]

**Deduction for this project.** Replacing just the bisection size by `b n`
leaves `max{b,1/6}n+O(log n)` in that construction, since `N` is approximately
`n/2`. Reaching `p` or `1/8` by this route requires a stronger lemma for
completing a side while keeping its prescribed boundary available.
The missing theorem concerns the side's structure and boundary together;
it is not another numerical improvement of the bisection theorem.

## The sharper subcubic conversion and its limits

Makedon–Sudborough identify cutwidth with edge-search number for maximum degree
three graphs; Ellis–Sudborough–Turner prove
`vs(G) <= s(G) <= vs(G)+2` for connected undirected graphs.
Together with `vs=pw`, these imply the table's `+2` conversion.
The original publisher abstracts were read; original proofs were not recovered.
The precise chain is independently explicit in the full proof of Lemma 16 of
Bodlaender et al. (2025), which cites Corollary 3.3 and Theorem 2.1 of the
respective originals. [makedonsudborough89][makedonsudborough89]
[ellis94][ellis94] [kinnersley92][kinnersley92] [bodlaender25][bodlaender25]

This is an external existence/conversion result, not a checked Lean replacement
for the repository's explicit median construction. Recovering the originals
or supplying a direct checked proof is required before changing that lemma.
Parallel edges and weighted edges should not be silently included: the existing
simple-cubic compression route already supplies a safe interface.

Bodlaender et al. also prove, for cubic `G` and `H=L(subdivide_once(G))`,
`cw(G) <= cw(H) <= cw(G)+2` and
`pw(G) <= pw(H) <= pw(G)+4` (Lemma 16).
Their graph `H` has `3n` vertices, so a universal coefficient measured against
`|V(H)|` incurs a factor of three when transferred back. This transformation
is useful for testing related parameters, not automatically for reducing `p`.
[bodlaender25][bodlaender25]

## Edwards–McDermid: a real template with a real range restriction

Their degree weight satisfies `g_alpha(2)=0`, `g_alpha(3)=alpha`, and
`d*g_alpha(d)=(d-2)*g_alpha(d-1)+g_alpha(d-2)+1`.
Theorem 3.2 uses `1/6 <= alpha <= 3/10`; Corollary 5.2 yields
`pw(G) <= sum_v g_(1/6)(deg_{r(G)} v)+o(|V(G)|)` after their series-parallel
reduction `r(G)`. Section 3.1 explicitly identifies failure of decreasing
increments outside that interval. The theorem and proof structure were read.
[edwardsmcdermid15][edwardsmcdermid15]

**Deduction.** Already at degree four,
`g_alpha(4)-g_alpha(3) - (g_alpha(3)-g_alpha(2)) = 1/4-3alpha/2`.
This is positive at `alpha=p` and `alpha=1/8`. More generally, any replacement
degree-only weights with `g_2=0`, `g_3=alpha`, decreasing increments, and
unit deletion payment `4g_4-2g_3>=1` force `g_4<=2alpha` and hence
`6alpha>=1`. A richer potential or a different treatment of degree-four
configurations is needed. This is a barrier to those particular inequalities.

Raw cutwidth has an additional problem with the framework's unit cost for
deleting a vertex: a star has `cw(K_(1,d))=ceil(d/2)` but deletion of its
center leaves cutwidth zero. Thus an abstract parameter theorem with
`q(G)<=q(G-v)+1` cannot be instantiated with cutwidth on general graphs.
For pathwidth that unit inequality is valid, but converting back at high
degree reintroduces a degree-dependent cost.

## Cycle rank and trees: where additive terms really matter

The spanning-tree argument gives, directly, `cw(G)<=beta_1(G)+cw(T)` for a
connected graph: add each non-tree edge back into a layout of `T`, paying
at most one per frontier. This is a deduction, not a newly discovered result.
It explains why improved tree layouts or exact treatment of hanging trees
improve finite thresholds and errors while leaving the coefficient of
`beta_1` equal to one in that argument.

Chung's 1985 theorem relates tree cutwidth `f(T)` to topological bandwidth:
`b*(T)<=f(T)<=b*(T)+log_2 b*(T)+2`, with near-tight examples.
Chung–Seymour (1989) give bounded cutwidth under bounded maximum degree and
exclusion of subdivisions of a fixed complete binary tree. The first paper's
theorem was checked from primary source text; the second was screened at its
publisher abstract. These are structural tree/obstruction tools, not universal
linear improvements for cubic expanders. [chung85][chung85] [chungseymour89][chungseymour89]

“Cycle-rank” also names a different recursive parameter in directed graph and
searching literature. Here it always means `|E|-|V|+components`, the dimension
of the cycle space. A theorem about directed elimination cycle-rank must not
be imported solely because the names match.

## What the 2025 lower-bound paper can and cannot obstruct

Bermond–Cosnard–Coudert–Havet Proposition 11 gives
`cw(G)>=C*(m,n)=min{C:m<=T(C,n)}`, where `T(C,n)` is the maximum number of
edges in a simple `n`-vertex graph of cutwidth at most `C` (Proposition 10).
Their Proposition 13 computes this lower bound in `O(log n)` arithmetic steps.
The full HAL manuscript was read, especially Propositions 5 and 10–13.
[bermond25][bermond25]

**Cubic specialization.** Their formulas `T(2,n)=floor((3n-3)/2)` and
`T(3,n)=2n-3` imply `C*(3n/2,n)=3` for even `n>=6`.
Their minimum-degree bound gives `4` when minimum degree is three.
Thus these particular global density bounds remain constant on cubic graphs;
they do not obstruct either `p n` or `n/8+o(n)`. Dense-subgraph enhancements
are valuable in general optimization, but cubic subgraphs still have maximum
degree three. [bermond25][bermond25]

The serious linear obstruction for this project comes from expansion/bisection
families, discussed in the [spectral review](../spectral/index.md), rather than
from density alone. A lower bound for a single finite graph also cannot refute
an asymptotic statement with arbitrary positive slack and an unspecified threshold.

## Research priorities from the classical branch

1. Formulate an anchored layout theorem for subcubic pieces that records boundary
   degrees and already exposed edges, and test whether it beats the `N/3`
   term in Lemma 4. This is the clearest classical opening to a better bridge.
2. Optimize complete orders on small cubic cores using the
   [exact and SDP tools](algorithms.md), retaining a witnessed order and every
   prefix boundary. Use failures to improve local rules; finite success is not
   a universal theorem.
3. If extending the cubic result to higher degrees, redesign the
   Edwards–McDermid potential with additional local structure. Merely lowering
   `g_3` breaks a verified inequality at degree four.
4. Treat `+2` versus `+4`, exact trees, and small-core exceptions as finite-error
   improvements. They are worthwhile but cannot deliver the `5n` coefficient.

## Known limitations

Search coverage is substantial but neither exhaustive nor a priority certificate.
The main statement is about sources actually recovered through 2026-10-09.
Access depth varies: the core Fomin–Høie, Edwards–McDermid, and recent
optimization arguments were read in full or in full relevant sections; some
historical conversion papers were available only as publisher abstracts.
No production Lean theorem was changed, and no new universal bound was proved.

[bermond25]: ../sources.md#bermond25
[bodlaender25]: ../sources.md#bodlaender25
[chung85]: ../sources.md#chung85
[chungseymour89]: ../sources.md#chungseymour89
[diaz02]: ../sources.md#diaz02
[edwardsmcdermid15]: ../sources.md#edwardsmcdermid15
[ellis94]: ../sources.md#ellis94
[fominhoie06]: ../sources.md#fominhoie06
[kinnersley92]: ../sources.md#kinnersley92
[korachsolel93]: ../sources.md#korachsolel93
[makedonsudborough89]: ../sources.md#makedonsudborough89
[monienpreis06]: ../sources.md#monienpreis06
[petit11]: ../sources.md#petit11
