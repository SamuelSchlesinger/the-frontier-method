# Threshold-coherent local optimization: a concrete research route

[Back to spectral review](index.md). These are deductions and proposals for this
project, not a published improvement of the universal cubic cutwidth coefficient.
The deterministic argument below is written out; its probabilistic gain is open.

## Why nested min-cuts are relevant

The existing `Frontier/Layouts/Local.lean` replaces keys at an independent set by
neighbour medians. Every threshold cut improves simultaneously. A bounded patch
can use the same idea with an exact local cut optimization instead of one median.
The useful precedent is parametric flow and the discrete coarea correspondence,
especially Chambolle–Darbon Proposition 3.3. [chambolle-darbon2009][chambolle-darbon2009]
Gallo–Grigoriadis–Tarjan supplies the classical parametric-flow algorithmic
framework. [gallo-grigoriadis-tarjan1989][gallo-grigoriadis-tarjan1989]

## Deterministic patch lemma, proved here

Let `P` be a finite vertex patch, with all exterior keys fixed. Initially take
unweighted edges and assume each component induced on `P` touches its boundary.
For threshold `t`, let `B_t` be the exterior vertices whose keys are below `t`.
For `S ⊆ P`, let `f_t(S)` count cut edges having at least one endpoint in `P`,
when `S` is the interior side and `B_t` is the exterior side.
Choose the **inclusion-maximal** minimizer `S_t` of `f_t`.

These minimizers exist and are nested as `t` increases. To see this, write
`f_t(S) = cut_P(S) + sum_{v in S} h_t(v) + constant_t`, where
`h_t(v) = number of exterior neighbours - 2*(number in B_t)`.
The functions `h_t` are nonincreasing in `t`. Cut submodularity gives, for `t ≤ u`,

`f_t(S) + f_u(T) ≥ f_t(S ∩ T) + f_u(S ∪ T)`.

If `S,T` minimize the respective functions, equality must hold and `S ∪ T`
is a minimizer at `u`. Maximality of `T` forces `S ⊆ T`. Taking `t=u` also
shows closure of the minimizers under union, proving the unique maximal choice.

The objective changes only at exterior key values. Below every boundary key,
the unique minimizer is empty; above every boundary key, it is `P`. Thus each
interior vertex has a new real key, selected from the boundary keys, whose
strict sublevel sets are precisely `S_t`. Group equal boundary keys together;
the same construction works at ties with the convention `key < t`.

The old interior threshold set is feasible, so `f_t(S_t) ≤ f_t(S_old)` for
**every** threshold. If patches are disjoint and have no edges joining them,
their affected edge sets are disjoint, and these gains add exactly. This proves
an all-threshold improvement of one scalar-key layout on any finite graph,
including parallel edges. Nonnegative edge weights are also allowed if each
interior component in the positive-weight support reaches the exterior through
positive-weight edges; this condition justifies the unique extreme minimizers.
For a one-vertex cubic patch this reduces to the neighbour-median update.

A component with no exterior boundary can be handled separately. For this
proposal it is simpler to exclude it from patch selection; bounded components
also have bounded cutwidth and do not govern an asymptotic coefficient.

## Locality and ties remain manageable

Choose patches of bounded radius, with centres separated enough that no two
patches touch by an edge. Independent random priorities can make such a choice
locally: a centre is selected when its priority is the minimum in a sufficiently
large fixed-radius ball. A bounded number of deterministic colour classes of
a graph power gives another schedule. These are proposed schedules, not claims
of optimal packing density.

If initial keys are medians of Gaussian edge scores, a new key is one of finitely
many original edge scores in a bounded neighbourhood. For an interval of length
`δ`, a union bound gives `P(new key is in interval) ≤ K δ/sqrt(2π)`, where `K`
depends on the fixed patch radius and initial score radius. No independence
between the candidate scores is needed. The same observation controls tails.
Bounded-radius selection and scores leave a bounded dependency graph, hence
variance `O(n)`. The repository's finite-grid concentration mechanism can then
recover all prefixes, including those cutting through equal-key groups.

This locality restriction matters. Global graph total-variation denoising can
collapse a linear number of vertices to one key. Its threshold cuts can all be
small while a tie-breaking ordering has a large interior cut. A nested family
alone does not solve that problem; the bounded-support window argument does.

## An explicit threshold profile, deduced here

For standard jointly Gaussian `X,Y` with correlation `r ∈ (-1,1)`, let
`q_r(t)=P(X<t≤Y or Y<t≤X)`. Direct Gaussian differentiation gives

`q_r(t) = (1/π) integral_{r}^{1} exp(-t²/(1+s))/sqrt(1-s²) ds`.

One verification is to write `q_r(t)=2(Φ(t)-Φ_2(t,t;r))`, differentiate the
bivariate density using `∂_r φ_r = ∂_x∂_y φ_r`, integrate twice, and use the
limit `q_1(t)=0`. This is the classical normal-integral differentiation route
associated with Plackett; only metadata for that source was accessible here,
so the displayed differentiation is the argument used in this note.
[plackett1954][plackett1954]

Since `1+s ≤ 2`, it follows that
`q_r(t) ≤ exp(-t²/2) arccos(r)/π`.
If `r=1`, the two scores coincide almost surely and both sides are zero, so
the inequality extends to this endpoint by continuity or direct inspection.
Applying this pairwise before the repository's star-angle estimate yields
`E[straddlers(t)] ≤ (p + ε) exp(-t²/2) n`
for its finite-radius parameters. This strengthens the threshold profile,
but its maximum is still the existing constant `p` at zero.
The argument is not formalized in Lean in this review.

Consequently a stronger universal coefficient only needs additional gain in
a bounded central band. For a proposed target `c<p`, the baseline profile is
already below `c` whenever `|t| > sqrt(2 log(p/c))`, ignoring the adjustable
finite-radius slack. For `c=1/8`, that cutoff is about `0.4813`.

## The exact missing probabilistic lemma

Let `B_t` be the original straddler count, `C_t` its actual median cut, and
`G_t` the total gain from the chosen patches. A sufficient new estimate is

`E[B_t - C_t + G_t] ≥ η n` for every `|t| ≤ t0`, uniformly over cubic graphs,

for fixed positive `η,t0` and finite score/patch parameters chosen so that
their approximation error is smaller than `η`. Combined with a strict deficit
outside the band and the window argument, this gives a smaller universal
coefficient. The baseline deficit and patch gain should be optimized together:
short cycles might reduce `B_t` while also destroying a particular gain event.
Neither a positive tree probability nor successful finite graph experiments
establish this uniform estimate.

The smallest useful search space is radius-one or radius-two patches, with
their external Gaussian covariance matrices. Enumerate all short-cycle
identifications; minimize the combined deficit plus gain over a proved
outer approximation of the feasible covariance set. A certificate must include
singular boundary matrices, threshold intervals, and quadrature error.
Allowing every positive semidefinite matrix may discard indispensable
distance-kernel constraints and produce a false obstruction to the method.

## Exact accounting blocks one tempting shortcut

For any cubic graph and any threshold, colour edges by whether their scores
are below threshold and vertices by the majority incident edge colour.
Each straddling vertex has one minority edge. A crossing edge is minority at
exactly one endpoint; an edge minority at both endpoints does not cross.
Therefore, with `D_t` the number of these double-minority edges,

`B_t = C_t + 2 D_t`.

For the cubic Gaussian wave at adjacency eigenvalue `λ=2sqrt(2)`, normalized
edge scores are proportional to endpoint sums. At a fixed edge, the four other
incident scores sum to `(λ+1)` times its score. At threshold zero, a central
score cannot have the opposite sign from all four others. Thus `D_0=0` almost
surely in this limiting tree process. Tightening the charging inequality alone
cannot lower the critical value for those unchanged scores. A nonlinear key
change or a different joint score distribution is needed.

## Validation and limitations

[check_proposals.py](data/check_proposals.py) checks the charge identity on all
1,088 Boolean edge assignments of three small cubic graphs and checks nested
maximal patch minimizers on 15,360 threshold instances from 640 graphs.
It also computes the spectral target, threshold band, and entropy arithmetic.
[Saved output](data/check_proposals-output.json) records the results. These are
finite sanity checks accompanying the proofs above, not an asymptotic gain
certificate. No production Lean statement or claimed cutwidth bound was changed.

[chambolle-darbon2009]: ../sources.md#chambolle-darbon2009
[gallo-grigoriadis-tarjan1989]: ../sources.md#gallo-grigoriadis-tarjan1989
[plackett1954]: ../sources.md#plackett1954
