# Spectral, Gaussian, and probabilistic routes

[Research overview](../index.md) · [Threshold-coherent patch optimization](patches.md)
· [Search and access log](data/search-log.md).
Reviewed against the current Gaussian and local-layout Lean introductions and
the Gaussian-layout section of `paper/frontier.tex`, on 2026-10-09.

The most useful literature supports **nonlinear, local improvements of one
real-valued score process**. It does not presently supply a verified replacement
for the repository's universal coefficient `p = 0.1403509686358236`.
The spectral endpoint already limits a straightforward improvement of the
unchanged Gaussian-star proof. The central open task is a uniform gain theorem
covering arbitrary cubic neighbourhoods and every relevant threshold.

## Applicability map

| Method or result | What is actually controlled | What remains for this project |
|---|---|---|
| Gaussian waves / FIID approximation | Local distributions on the regular tree and sufficiently tree-like graphs | Arbitrary short cycles and one coherent order |
| Lyons local sign improvements | Minimum/maximum bisection along graph sequences converging locally to a tree | Uniform threshold gain beyond the current edge-median bound |
| Lichev–Mitsche `0.139822n` | Minimum bisection of random cubic graphs | Nested choices and arbitrary-graph covariance control |
| Nonbacktracking / polynomial filters | A different local score distribution, with tree spectral analysis | A new extremal objective or a useful finite-radius improvement |
| Independent neighbour medians | All threshold cuts of one key assignment weakly improve; already checked locally | A positive uniform expected improvement |
| Bounded-patch min-cuts | Nested threshold optimizers; deterministic extension proved in [the detail note](patches.md) | Certified gain, patch selection, and formal integration |
| Spin-glass interpolation | Random-graph extremal cut densities or bounds | Neither arbitrary graphs nor a layout transfer is supplied |
| FIID entropy inequalities | Necessary conditions on local processes | Useful barriers, but they do not rule out `p=1/8` |

## What Gaussian waves contribute

Csóka, Gerencsér, Harangi and Virág construct invariant Gaussian waves on the
`d`-regular tree and show that waves with adjacency eigenvalue
`|λ|≤2sqrt(d−1)` are weak limits of linear factors of IID. Their Theorem 4 is
the appropriate source for the approximation mechanism. Their independent-set
application is not a cutwidth theorem. [cghv2015][cghv2015]

For positive endpoint eigenvalue `λ=2sqrt(2)`, the cubic-tree neighbour
correlation is `r1=2sqrt(2)/3`, and the distance-two correlation is `r2=5/6`.
The repository combines normalized endpoint sums into edge scores and orders
vertices by their incident medians. Its additional ingredients are a kernel
bound valid without a girth assumption and simultaneous control over a finite
threshold grid, windows, and tails. Tree approximation alone supplies neither.

Lyons Theorem 4.1 applies to finite graphs whose random weak limit is the
regular tree and whose average degree tends to `d`. It proves strict local
improvements over the Gaussian-sign bisection value; for cubic graphs the
unimproved value is `3 acos(2sqrt(2)/3)/(2π)=0.1622601719...`.
The proof transfers bounded-radius rules and repairs an `o(n)` imbalance.
That transfer is useful for large essential girth, rather than a theorem for
every cubic graph. [lyons2017][lyons2017]

Lichev–Mitsche Section 6 improves random-cubic minimum bisection to `0.139822n`
asymptotically almost surely. It identifies vertices with two crossing incident
edges under Gaussian signs, chooses compatible exchanges using an auxiliary
bipartite graph, and balances the two sides. Its later Monte Carlo refinement
is explicitly non-rigorous. The article appeared in 2023, although the preprint
and the repository bibliography key use 2020. [lichev-mitsche2023][lichev-mitsche2023]

**Transfer assessment:** that exchange choice is made for a single sign cut.
Choosing a different compatible exchange set at each threshold need not yield
nested cuts. The literature therefore gives a valuable gain mechanism, but its
displayed constant cannot be inserted into the existing all-prefix theorem.

## A precise spectral obstruction, and its scope

Backhausz–Szegedy–Virág bound correlations of invariant finite-variance FIID
processes on the `d`-regular tree by
`|corr(X_u,X_v)|≤(k+1−2k/d)(d−1)^(−k/2)` at distance `k`.
At distance one this is `2sqrt(d−1)/d`, independently of the rule's radius.
This also covers nonlinear FIID outputs as a correlation restriction.
[backhausz-szegedy-virag2015][backhausz-szegedy-virag2015]

Backhausz–Virág characterize FIID spectral measures on vertex-transitive
graphs: they are exactly the measures absolutely continuous with respect to
the graph spectral measure. Their weak-limit characterization allows measures
supported on the spectral support. Gaussian waves at an endpoint are limits,
not ordinary square-summable endpoint eigenvectors. The polynomial description
of radial factors gives the natural framework for filter optimization.
[backhausz-virag2017][backhausz-virag2017]

**Deduction for the unchanged proof.** Its star expression
`p(r)=3 acos((1+3r)/4)/(2π)` would require
`r≥(4 cos(π/12)−1)/3=0.9545677684...` to reach `p=1/8`.
This exceeds the tree FIID limit `0.9428090416...`. Increasing the radius,
changing a radial filter, or improving its numerical eigenvalue approximation
cannot establish that stronger correlation on all large-girth cubic graphs.

There is a slightly stronger statement for the **straddler objective** of
invariant Gaussian vertex scores followed by normalized endpoint sums on the
tree. If the unit-mass spectral measure has support in `[-sqrt(8),sqrt(8)]`,
then `r1≤sqrt(8)/3` and `r2≤5/6`. The common incident-edge correlation is
`c=(1+2r1+r2)/(2+2r1)`, increasing in both variables whenever defined and
`r2≤1`. Thus `c≤(1+2sqrt(2))/4`, and the zero-threshold straddler probability
is at least the present `p`. This is a deduction about that Gaussian objective,
not a lower bound on cutwidth or on nonlinear local layouts.

Polynomial/Chebyshev or nonbacktracking filters are still useful for smaller
support at a given approximation error, for different graph classes, or as
inputs to nonlinear postprocessing. The directed-message formulation in
El Alaoui–Montanari–Sellke explicitly recovers finite Gaussian-wave
approximations as a special case. [el-alaoui-montanari-sellke2023][el-alaoui-montanari-sellke2023]
On arbitrary graphs, graph-dependent normalizations and short closed walks
must be included in a covariance proof; a tree Rayleigh quotient does not give
the repository's pointwise adjacent-row bound automatically.

## The best next route: coherent local improvement

The checked `cutSize_improve_cubic_le` already allows an independent set of
vertices to replace their keys by neighbour medians. Each threshold cut weakly
improves. Choosing vertices by independent priority minima gives inclusion
probability `1/4` in a simple cubic graph, independently of the Gaussian scores.
For a fixed threshold, the expected gain is therefore one quarter of the sum
of the available local gains. The deterministic identity is in
`Frontier/Layouts/Local.lean`; the required uniform stochastic estimate is not.

**Quantitative target.** Reaching `p=1/8` solely by that one-round priority rule
would require mean available local gain at least `4(p−1/8)=0.0614038745...`
per vertex at the critical threshold, before approximation losses. A smaller
gain still improves the circuit coefficient `1+1/(2p)`. These are arithmetic
requirements, not evidence that the required gain occurs.

A stronger concrete candidate is **exact optimization on bounded patches**.
Parametric min-cut and the discrete coarea principle supply compatible nested
solutions as the fixed boundary threshold moves. Our [detail note](patches.md)
proves the deterministic patch extension, gives a finite-dependence/window
argument, and specifies the missing gain inequality.
[chambolle-darbon2009][chambolle-darbon2009]
[gallo-grigoriadis-tarjan1989][gallo-grigoriadis-tarjan1989]
Because the output keys can be selected from local boundary keys, this route
can preserve the existing concentration architecture.

The note also derives `E[straddlers(t)]≤(p+ε)exp(−t²/2)n`. The maximum remains
at zero, but an improvement need only be certified in a central band; for a
`1/8` target its limiting half-width is `0.4813158361...`.
This is an unformalized deduction from bivariate Gaussian differentiation,
not an improved universal leading constant. [plackett1954][plackett1954]

An exact counting identity gives `straddlers = actual median-cut size + 2D`,
where `D` counts edges minority at both endpoints. On the extremal tree wave
at zero, `D=0`: the four surrounding edge scores sum to a positive multiple
of the central score. Thus improved charging alone cannot create a saving at
the critical distribution. The detail note supplies the proof and finite checks.

## Covariance comparison and numerical certification

More correlation does not monotonically improve every **mixed-sign** event.
For three centred standard Gaussians, the probability of the sign pattern
`(+,-,-)` equals
`1/8 + (−asin r01−asin r02+asin r12)/(4π)`.
Increasing centre–leaf correlation reduces this probability, whereas increasing
leaf–leaf correlation raises it. The formula follows directly by expanding the
three sign indicators and applying the bivariate Gaussian angle identity.
Componentwise covariance domination is therefore insufficient for a blanket
claim that the tree is worst for the improvement event.

A realistic certificate should optimize **baseline deficit plus gain**, retaining
positive semidefiniteness, distance-kernel relations, neighbourhood identifications,
and singular cases. A numerical optimum over a convenient covariance cone is
a conjecture until the cone includes every realizable local configuration and
the integral/optimization errors are bounded. Certified central-band estimates
would be much more valuable than another unqualified zero-threshold simulation.

Janson provides exponential concentration for sums with a suitable dependency
structure. This could replace second-moment bounds to reduce finite-size
thresholds or support growing radii, but concentration changes fluctuations,
not the limiting mean coefficient. The source's detailed theorem was not
accessible here, so no numerical finite-size claim is based on it.
[janson2004][janson2004]
Global SDP embeddings need a separate simultaneous-rounding or concentration
argument; their coordinates need not have bounded dependence. See the
[classical review](../classical/index.md) for cutwidth-specific SDP methods.

## Spin glasses, message passing, and current related results

Dembo–Montanari–Sen prove the random-regular large-degree minimum-bisection
asymptotic `n(d/4−P_*sqrt(d)/2+o_d(sqrt(d)))+o_n(n)`, with
`P_*≈0.7632`, using interpolation with the Sherrington–Kirkpatrick model.
Their companion maximum-cut and maximum-bisection results have the opposite
sign. The large-degree remainder is uncontrolled at `d=3`; plugging in three
does not create a cubic theorem. [dembo-montanari-sen2017][dembo-montanari-sen2017]

El Alaoui–Montanari–Sellke develop nonlinear directed-message algorithms for
large-degree locally tree-like regular graphs. **Theorem 1.7 in the accessed
full text assumes a strictly increasing minimizer of the SK Parisi functional.**
The algorithmic guarantee is conditional on that assumption and asymptotic in
degree. Its final balanced two-colouring is not an all-threshold scalar layout.
The useful import is a family of nonlinear local rules to study at fixed degree.
[el-alaoui-montanari-sellke2023][el-alaoui-montanari-sellke2023]

Barak–Marwaha compare local classical and quantum maximum-cut algorithms on
high-girth regular graphs, including a limitation for centred one-local
distributions and stronger multi-round classical constructions. This warns
against treating a one-step local bound as a limit on arbitrary-radius rules.
Its maximum-cut guarantee does not transfer to minimum cut by complementing
one side in a nonbipartite cubic graph. [barak-marwaha2022][barak-marwaha2022]

Zdeborová–Boettcher propose a random-regular complement relation between
maximum cut and minimum bisection. It is a physics-motivated conjecture in the
source, not a general graph identity. [zdeborova-boettcher2010][zdeborova-boettcher2010]
Coja-Oghlan–Loick–Mezei–Sorkin prove interpolation upper bounds for random
regular **maximum** cut. Harangi's 2025 preprint improves these using 2-RSB;
its cubic maximum-cut fraction is at most `0.92386` asymptotically.
[coja-oghlan-etal2022][coja-oghlan-etal2022] [harangi2025][harangi2025]
Even with the complement conjecture, this would give a minimum-bisection
**lower** bound near `1.5(1−0.92386)n=0.11421n`, not a layout upper bound.

The 2026 Aronow–Lopatto preprint proves that random-regular maximum cut and
**maximum bisection** have the same limiting density for each fixed degree.
Theorem 1.1 does not establish the minimum-bisection complement conjecture,
and gives no new all-graph ordering guarantee. [aronow-lopatto2026][aronow-lopatto2026]

## Entropy and expansion barriers

Backhausz–Gerencsér–Harangi develop entropy constraints for factors of IID,
including generalizations of the edge–vertex inequality
`(d/2)H(edge)≥(d−1)H(vertex)`. For a balanced binary cubic-tree factor with
edge-disagreement probability `q`, this gives `H_binary(q)≥1/3`.
Consequently `q≥0.0614904701...` and the cut density is at least
`3q/2≥0.0922357051...`. This calculated necessary condition is weaker than
known random-cubic bisection obstructions and leaves `1/8` feasible. Stronger
entropy inequalities could screen candidate local distributions; they are
not a proof that the current Gaussian constant is optimal.
[backhausz-gerencser-harangi2019][backhausz-gerencser-harangi2019]

For a finite graph with even `n`, the elementary Laplacian Rayleigh argument
gives `cw(G)≥λ2(L)n/4`: apply the spectral gap to the centred indicator of the
middle cut. This is a lower-bound certificate. Spectral separators and
recursive layouts have a different role, discussed in the
[structural review](../structural/index.md). An expander's spectral gap should
not be mistaken for a small-boundary supply theorem.

## Validation and limitations

[Reproducible checks](data/check_proposals.py) and [output](data/check_proposals-output.json)
verify the numerical deductions, the median charge identity on all Boolean
assignments of three cubic examples, and nested patch choices on 640 small
graphs. They do not certify a universal positive gain. The strongest load-bearing
papers were inspected in full text at the stated theorems/sections; abstracts
alone are explicitly marked in the references. This is targeted coverage of
the most relevant mechanisms, not a claim to have read every graph-probability
paper. Existing project-only high-girth/covariance computations require their
own archive audit and are not external theorems in this review.

[aronow-lopatto2026]: ../sources.md#aronow-lopatto2026
[backhausz-gerencser-harangi2019]: ../sources.md#backhausz-gerencser-harangi2019
[backhausz-szegedy-virag2015]: ../sources.md#backhausz-szegedy-virag2015
[backhausz-virag2017]: ../sources.md#backhausz-virag2017
[barak-marwaha2022]: ../sources.md#barak-marwaha2022
[cghv2015]: ../sources.md#cghv2015
[chambolle-darbon2009]: ../sources.md#chambolle-darbon2009
[coja-oghlan-etal2022]: ../sources.md#coja-oghlan-etal2022
[dembo-montanari-sen2017]: ../sources.md#dembo-montanari-sen2017
[el-alaoui-montanari-sellke2023]: ../sources.md#el-alaoui-montanari-sellke2023
[gallo-grigoriadis-tarjan1989]: ../sources.md#gallo-grigoriadis-tarjan1989
[harangi2025]: ../sources.md#harangi2025
[janson2004]: ../sources.md#janson2004
[lichev-mitsche2023]: ../sources.md#lichev-mitsche2023
[lyons2017]: ../sources.md#lyons2017
[plackett1954]: ../sources.md#plackett1954
[zdeborova-boettcher2010]: ../sources.md#zdeborova-boettcher2010
