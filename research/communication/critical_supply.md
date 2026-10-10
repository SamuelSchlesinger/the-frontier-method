# Critical transition supply, including supplied parity inputs

The universal quarter-coefficient supply theorem and preservation of the full
`4.562497...n` circuit bound under an arbitrary linear number of redundant free parity
inputs remain unproved here. This investigation gives two structural supply
certificates, an obstruction to a proposed Gaussian shortcut, and checked
parity-invariance results with their exact scope. The matching route now also
proves an explicit improvement over the original Gaussian supply and circuit
coefficients: a supply saving of `10^-48` gives a circuit-coefficient gain of
at least `10^-47`. It also preserves the old coefficient with up to `10^-48 n`
free extra parities in the consistent-pair model.

`Frontier/Parity.lean` verifies preservation of cardinality, sumset-freeness,
additive charging demand, and the full circuit bound under an invertible
additive input basis. `Frontier/Boundary/Forest.lean` verifies the forest capacity
certificate, its exact rank formula, and its use for complete transition codes.
`Frontier/Compiler/Source.lean` now constructs and counts that forest in a compressed
circuit, and `Frontier/Compiler/Forest.lean` proves its capacity bound for actual
traces with nonconstant signals. `Frontier/Boundary/Syndrome.lean` constructs a
sweep enforcing an additive promise at the cost of one syndrome per transition.
`Frontier/Boundary/Observation.lean` now proves the exact joint rank of visible
input coordinates and that syndrome, and applies it to the promise-enforcing
sweep. The charge-only encoding interface is also checked in `Boundary/Code.lean`.
`Frontier/Layouts/Patch.lean` now checks simultaneous patch optimization, including
one objective for the signal boundary and parity consistency, and explicitly
accounts for ties when passing from thresholds to prefixes.
`Frontier/Layouts/GaussianPatch.lean` now proves a uniform expected-cost improvement
for the symmetric two-vertex Gaussian model. This is a local probability theorem;
`Frontier/Layouts/KernelRigidity.lean` now proves the covariance under exact
critical edge ratios, including a dimension-independent near-saturation estimate.
`KernelStability.lean` and `KernelCovariance.lean` now account for the ratio errors
of actual finite normalized kernels. `StarStability.lean` controls both adjacent
correlation gaps and star residuals by the gap in the three-edge star inequality.
The resulting covariance estimate needs only two measured star gaps, alongside
the stated kernel parameters. `Pair.lean` verifies the subdivision comparison
between the local energy and actual graph cuts, with explicit keys attaining
every threshold minimum. `StarSupply.lean` now keeps a large-gap saving through
concentration and the construction of a complete ordering. `Packing.lean`
supplies linearly many disjoint small-gap pairs in the complementary case.
`GaussianStability.lean` and `KernelPairStability.lean` now retain the local
pair saving under small covariance errors, and then under small star gaps in
actual finite kernels, uniformly over all thresholds. `MatchingGrid.lean` and
`MatchingGaussian.lean` now control one complete ordering, including windows,
tails, and ties. `MatchingSupply.lean` transfers the resulting strictly smaller
universal layout coefficient to a strictly larger circuit coefficient.
The fractional certificate remains a paper proof with exact finite checks.

## What a supply theorem must bound

Put `q=s-r`, where `r` is the number of reachable original inputs, and

```
A = (3/pi) arccos((1+2 sqrt(2))/4) = 0.28070193727164739269...
L = 1+1/A = 4.56249767892501858313...
M = (K-1)^2.
```

For the first threshold crossing `T(x)`, let `R_t` contain the complete
transitions realized by inputs charged at time `t`. Threshold charging gives
`|S| <= M sum_t |R_t|`. Thus five would follow from

```
sum_t |R_t| <= poly(n+s) 2^((s-r)/4+o(n)).                    (1)
```

A code determining the original transition cannot use fewer labels than
`|R_t|`. It can improve the raw wire bound, but relabelling alone does not
reduce this cardinality. Replacing the messages requires a new splicing proof.

Lean now checks this charge-only formulation as `Sweep.ncard_le_charged` and
`Sweep.ncard_le_charged_codes`. Their supply counts only transitions receiving
a first-threshold charge. The code-membership and determinacy hypotheses apply
only to inputs charged at the relevant step; other accepting inputs may collide
arbitrarily. The existing all-transition theorem follows by enlarging these
image sets. This refines the interface for (1), without proving its quantitative
upper bound.

For coherent nested sweeps there is a further exactness fact. Fix a realized
transition `e=(q,r,z)`, including its new input bits. Splice any past in the old
state with a representative's future, then splice the resulting past in the
new state with any future in the new state. Coherence preserves the relevant
trace segments. Consequently the transition fiber is exactly the product of
its old pasts and new futures, with `z` fixed:

```
|F_e| = a_t(q) b_(t+1)(r).
```

These product capacities are the actual trace loads. The input paths form a
flow of value `|S|`, and any whole-layer cut has capacity exactly `|S|`, so the
weighted minimum cut equals `|S|`. Past counts are nondecreasing; each trace
crosses the threshold once, and the critical cut also has total capacity
`|S|`. An upper bound on its *description cost* is the missing ingredient.

## A fractional local-constraint certificate

Let `R` be a nonempty set of bit patterns on `d` code coordinates. For each
scope `J`, suppose its projection lies in a known relation `A_J`. Give these
relations nonnegative weights satisfying

```
sum_(J containing i) lambda_J <= 1    for each coordinate i.
Delta = sum_J lambda_J (|J|-log_2 |A_J|).
```

Then

```
log_2 |R| <= d-Delta.                                       (2)
```

Proof: take the uniform random pattern on `R`. Add a singleton scope of
weight `1-sum_(J containing i) lambda_J` at each coordinate. This gives a
fractional cover of weight exactly one at each coordinate. The entropy chain
rule and conditioning give the fractional Shearer inequality; bound the
entropy on `J` by `log_2 |A_J|` and singleton entropy by one. Rearranging gives
(2). No independence hypothesis is used. For rational weights `lambda_J=m_J/b`,
the equivalent certificate has no logarithms:

```
|R|^b <= 2^(b d-sum_J m_J |J|) product_J |A_J|^m_J.           (3)
```

This is a standard fractional projection/entropy inequality, applied here to
frontier codes. See Mokshay Madiman and Prasad Tetali,
[Information Inequalities for Joint Distributions, with Interpretations and
Applications](https://arxiv.org/abs/0901.0044), IEEE TIT 56(6), 2010.

An AND input and output satisfy an implication with three allowed pairs, so
one unit of admissible weight saves `log_2(4/3)=0.415037...` bits. To close the
baseline gap using only such implications would require total weight at least

```
(A-1/4)/log_2(4/3) * q = 0.07397388748... q.                  (4)
```

The load condition is essential. For six outputs `Y_i=B AND X_i`, the joint
pattern `(B,Y_1,...,Y_6)` has 65 values. Charging all six implications at unit
weight would incorrectly bound this by `2^7(3/4)^6=729/32`. Their weights must
sum to at most one because they share `B`. Six disjoint implications, by
contrast, realize exactly `3^6` patterns and earn all six deficits.

## Preserve affine relations before using nonlinear constraints

The two-gate module `u=x_1 XOR x_2`, `z=u XOR x_3`, with visible signals
`x_1,x_2,x_3,z`, has eight patterns. Every proper projection is full. Inspecting
each gate separately and existentially forgetting `u` loses the entire bit of
saving. Composing the two gates recovers it.

More generally, for any fixed block budget `b`, a minimal XOR chain on `b+2`
inputs has `b+1` gates. Make only the original inputs and final output visible.
Every connected block of at most `b` gates has a full visible projection, while
the full relation saves a bit. Disjoint copies give a linear missed deficit.
This refutes completeness of bounded-block projection certificates, not the
existence of a better layout for hard circuits.

A sound combination proceeds as follows:

1. Treat each nonlinear gate output as a new formal bit, and propagate affine
   forms through all affine gates. This is a relaxation retaining every affine
   gate equation and all signal equalities.
2. Select a basis for the boundary observation forms, conditional on the known
   accepting output. If the output has nonzero formal linear part, the number
   of free code coordinates is
   `rank(boundary forms, output form)-1`.
3. Reconstruct any circuit signal whose form lies in that span, including
   signals physically outside the boundary. Translate projected nonlinear gate
   relations into these same code coordinates and apply (2).

The bound is `rank - Delta`. Adding an independently computed affine deficit
and an independently computed local deficit would risk charging the same
constraint twice. Basis choice can change the scopes and hence the available
fractional packing; the finite checker tries two basis orders, without claiming
an optimal basis or an efficient general optimization algorithm.

## A structural source of redundancy in the compressed core

Start with a two-input circuit, propagating constants and absorbing unary
operations into adjacent gates. Apply the existing connected-block compression
to its reachable acyclic network. If more than one block remains, its quotient
is a simple cubic graph `H` with `h<=2(s-r)` vertices. Retain the computational orientations of
the quotient edges. For a block `v`, put

```
u_v = number of incoming quotient edges + number of input sites in v.
U = {v : u_v=1}.
```

Every block has `u_v>=1`: otherwise its nonempty acyclic subnetwork would have
neither an original input nor an incoming edge. Also

```
sum_v u_v = 3h/2+r,
|U| >= h/2-r.                                                (5)
```

The second inequality follows by giving every vertex outside `U` a lower
contribution of two. Every block in `U` has its ports determined by one bit,
so its joint port relation has at most two patterns.

For a linear-size circuit computing the hard family, the existing Gaussian
layout and charging demand give `n <= (A/2)h+o(n)`. Since `r<=n`, (5) then
forces `|U| >= (1/A-1)n-o(n) = 2.562497...n-o(n)`. There are linearly many
such blocks; obtaining their savings in one layout is the unresolved step.

Moreover, `H[U]` is a forest. If it contained a cycle, the cycle edges together
with the indegree bound of one would force every cycle vertex to have exactly
one incoming cycle edge, no incoming edge from outside, and no original input.
The union of the original blocks would again be a nonempty acyclic subnetwork
with no source. Quotient orientations themselves need not be acyclic; this
argument uses the original circuit's acyclicity.

Assume all reachable circuit signals are nonconstant on the original cube,
as can be arranged by semantic constant simplification. All ports of a block
in `U` are then equal or complementary. For a cut `P`, let `b(P)` be its
number of crossing edges and `k_v(P)` the number incident to `v`. Define

```
g_U(P) = sum_(v in U) max(k_v(P)-1,0).
```

The equality/complement constraints on the crossing bits have rank exactly
`g_U(P)`: their overlap graph is a subgraph of the forest `H[U]`. Remove a leaf
star; at most one of its coordinates is shared with remaining stars, so its
`k_v-1` equations are independent of theirs. Induction proves the rank claim.
Therefore

```
log_2 |realized boundary patterns at P| <= b(P)-g_U(P).        (6)
```

The capacity argument in (6) is now formalized in
[`Frontier/Boundary/Forest.lean`](../../Frontier/Boundary/Forest.lean):

- `ForestBoundary.exists_bijective_restrict` constructs a coordinate code and
  proves that every assignment to its retained coordinates extends uniquely to
  a compatible boundary pattern. Empty scopes and uncovered coordinates are
  included.
- `ForestBoundary.finrank_incident_differences` proves the exact rank `g_U(P)`
  over any field, assuming the marked induced graph is a forest.
- `ForestBoundary.compatible_xor_of_one_bit` derives equality/complement
  compatibility from nonconstant one-bit port maps.
- `ForestBoundary.ncard_le_incident_xor` proves the integer form of (6),
  `|R| <= 2^(b-g_U)`, for any set `R` of realized Boolean patterns. This includes
  a set restricted to charged inputs.
- `Sweep.transitionCount_le_forest_codes` composes these bounds with the existing
  transition code theorem. Its hypotheses explicitly require the pattern to
  determine both messages and all newly read inputs.

The compiler instantiation is now checked as well:

- `Compiler.topologicalRank_src_lt_tgt` proves directed acyclicity, including the
  fanout junction chains. `Multigraph.Compression.oneSource_acyclic` proves the
  forest assertion using the least topological rank in each block; it does not
  assume that the full directed quotient is acyclic.
- `Compiler.card_le_twice_oneSource_add_inputs` proves the exact integer form
  `h <= 2(|U|+r)` for a connected final cubic core with at least two blocks and
  no reachable zero-arity gates.
- `Compiler.oneSource_determines` derives port determinacy from the circuit's
  local semantics by topological induction. `oneSource_xor` proves the
  equality/complement assertion for nonconstant Boolean ports.
- `Compiler.ncard_boundaryPatterns_le` proves (6) for every selected external
  edge set of a final compression and every input subset. Its nonconstant-signal
  hypothesis also rules out reachable zero-arity gates.
- `Compiler.ncard_image_le_oneSource` counts any information determined by those
  patterns, including a complete transition on its charged input set when the
  stated determinacy hypothesis is verified.

The abstract forest certificate accepts any boundary edge set. The compiler
instantiation above uses external edges of the compression. Turning it into a
full expanded layout bound still requires the internal-frontier overhead and the
improved common ordering in (7). Semantic constant normalization is also a
separate prerequisite for this version of the compiler certificate.

If constant signals remain, use their pins and equality equations in one rank
calculation. Summing the displayed star deficits in that setting can overcount
a shared pin. The checker explicitly distinguishes the two cases.

Expanding a core layout incurs the existing `O(log(n+s))` overhead: during a
block expansion, use the preceding whole-block cut code and record the changed
external ports and internal frontier. Thus (6) is a concrete semantic layout
objective whose savings arise from forced circuit structure.

For example, a theorem supplying

```
max_P [b(P)-g_U(P)] <= (A/2)h-gamma |U|+o(n)                 (7)
```

for a fixed `0<gamma<A`, with a common ordering, would give
`W <= (A-gamma)(s-r)+gamma r+o(n)`. For `r=n-o(n)` the resulting circuit
coefficient is `1+(1-gamma)/(A-gamma)`, strictly above `L`. Five would require
`gamma >= (4A-1)/3 = 0.04093591636...`. Equation (7) is unproved.

## Why star correlations alone cannot supply this gain

Take three unit Gaussian scores `E_1,E_2,E_3` with common correlation
`c in (1/2,1)`. At neighbor `i`, give the two other edges scores

```
F_ij = 2c E_i-E_j,   F_ik = 2c E_i-E_k.
```

These scores have unit variance, and each neighboring triple has exactly the
same pairwise correlation `c` as the central triple. The four other scores
around the central edge `i` sum to `4c E_i`. At
`c=(1+2 sqrt(2))/4`, this also gives the limiting local wave identity used by
the edge-score process.

Nevertheless, color each vertex by whether the median of its three scores
is negative. At threshold zero the center has at most one opposite-colored
neighbor, for every score realization without ties. If its signs are two
positive and one negative, each positive-index neighbor has two positive
scores. If all three are positive, neighbor `i` can be negative only when
`E_i < min(E_j,E_k)/(2c)`; because `2c>1`, at most one index can satisfy this.
Negating all scores gives the other cases. Thus `g_U` at the center is zero.

This rules out a positive uniform saving derived only from local star
correlations and these wave identities. It does not refute the actual
distance-kernel law on finite cubic graphs, a different layout, or (7).

## Optimizing a patch without losing the common ordering

The new checked statement in `Frontier/Layouts/Patch.lean` is a deterministic
step toward the layout supply theorem. Let `c` be a nonnegative integer-valued
submodular function on vertex sets, with `c(empty)=c(V)=0`. Fix a patch `P` and
initial real keys `k`. There are new keys `k'`, unchanged outside `P`, such that
for **every** threshold `t`, the set `{v : k'(v)<t}` minimizes `c` among all sets
agreeing with `{v : k(v)<t}` outside `P`.

The proof uses uncrossing. If `A` and `B` are minimizers for nested boundary
conditions, `A intersect B` is feasible for the earlier boundary and `A union B`
for the later one. Submodularity and minimality imply the union is also optimal
for the later boundary. Choosing the largest minimizer therefore makes the
chosen cuts nested. Preserve the empty cut explicitly; the full cut is already
the largest minimizer at the final boundary. A finite monotone family with these
endpoints has a real-key representation.

This is the classical monotone submodular optimization principle, specialized
and proved here for patch boundaries; see Donald M. Topkis,
[Minimizing a Submodular Function on a Lattice](https://pubsonline.informs.org/doi/10.1287/opre.26.2.305)
(1978). The graph algorithmic setting is also related to Gallo, Grigoriadis, and
Tarjan's [parametric maximum-flow algorithm](https://epubs.siam.org/doi/abs/10.1137/0218003)
(1989). These sources are credited for the underlying optimization framework;
the Lean development does not implement either paper's algorithm.

The main declarations are:

- `PatchLayout.exists_key_minimum`: the common key representation, with exact
  optimality at every threshold and fixed keys outside the patch.
- `Hypergraph.exists_key_patch_minimum`: specialization to signal hyperedges,
  with no bound on hyperedge arity.
- `Hypergraph.exists_key_patch_cut_le`: if each threshold has a feasible patch
  replacement costing at most `B`, one injective ordering has every prefix
  costing at most `B+d(M+|P|)`, where `d` bounds vertex incidence and `M` bounds
  original key multiplicity.
- `PatchLayout.card_ties_le_of_local`: if an updated vertex selects an old key
  in a specified scope, and each original vertex occurs in at most `L` scopes,
  the new key multiplicity is at most `M L`.

The tie terms are essential. Constant keys have zero cost at every strict
threshold, while an arbitrary ordering of their vertices can have large cuts.
The new prefix theorem pays for the vertices in the tied group explicitly.

For parity inputs, `Boundary/Observation.lean` proves

```
lambda(P) = rank L_P + rank L_(P^c) - rank L
lambda(P intersect Q) + lambda(P union Q) <= lambda(P) + lambda(Q).
```

`finrank_partialSyndrome` identifies this value with the actual partial syndrome
map whenever `ker R=range L`. Therefore signal-boundary size plus `lambda` is
also submodular, even when input coordinates are placed at arbitrary graph
vertices. `Hypergraph.exists_key_patch_syndrome_minimum` optimizes this combined
cost in one common ordering. This version adds the two costs; it does not assume
that the sharper joint-observation cost is submodular when the visible set also
changes with the cut. No surplus-gate bound or full parity preservation follows
without a further quantitative supply estimate.

The exact checker `python3 research/communication/patch_layout.py --check`
checks all 2,048 hypergraphs on four vertices with hyperedges of size at least
two. It verifies 28,672 minima, 79,872 nested-boundary comparisons, and 2,048
thresholds of numerical patch updates against an independent enumerating oracle.

An exploratory screen uses random cubic graphs, initial median-edge keys, and
repeated optimal three-vertex patches. Patch centers have pairwise distance at
least four, so simultaneously updated patches neither overlap nor share an edge.
The initial field is a finite-graph radial polynomial with its constant mode
removed; it is not the formal bounded-support Gaussian construction. The saved
`patch_layout_results.json` uses 64,000 vertices, radius 40, and seed 1061:

| Patch rounds | Largest threshold cut / vertices | Largest prefix cut / vertices | Largest tie |
| --- | --- | --- | --- |
| 0 | 0.143343750 | 0.143359375 | 2 |
| 128 | 0.125546875 | 0.126015625 | 200 |
| 256 | 0.124859375 | 0.125484375 | 773 |

The largest prefix still exceeds `1/8`; this is not a certificate for the target
coefficient, even for this finite graph. It also illustrates why the cut at zero
alone is misleading: its final value is only `0.0883125`. A universal proof needs
a bound uniform in thresholds for the actual local random process, a transfer
to every relevant finite graph, and control of tie groups. The formal patch and
tie lemmas establish deterministic parts of that route, without those estimates.

## A checked uniform estimate for two adjacent vertices

There is now a quantitative local result in
[`Frontier/Layouts/GaussianPatch.lean`](../../Frontier/Layouts/GaussianPatch.lean).
For four outer port colors `a,b,c,d`, optimize the colors `u,v` of two adjacent
cubic vertices. The energy is

```
cost = min_(u,v) ([u!=a]+[u!=b]+[u!=v]+[v!=c]+[v!=d]).
```

Writing `I_ij` for pair disagreement, the exact identity is

```
cost = (I_ab+I_cd)/2 + (I_ac+I_ad+I_bc+I_bd)/4 + I_ab I_cd/2.  (10)
```

`four_mul_twoVertexCost` checks the identity with denominators cleared, and
`twoVertexCost_eq_minimum` checks attainability and optimality. Its expectation
formula `integral_twoVertexCost` is valid under any finite measure and measurable
Boolean port functions. The intersection term in (10) is essential.

For the probability estimate take independent centered Gaussians `X,Y,D,E`,
of variances `s,v,r,r`, and outer scores

```
X+cY+D, X+cY-D, Y+E, Y-E.
```

Both pairs straddling `t` implies `|X+cY-t|<=|D|` and `|Y-t|<=|E|`.
For fixed half-widths, condition on `Y` and use the peak density of `X`,
then the peak density of `Y`. Integrating the widths uses the exact Gaussian
absolute first moment. The resulting bound is uniform in every real threshold:

```
Pr[both pairs straddle t] <= 4r / (pi^2 sqrt(sv)).             (11)
```

No claim that zero is the worst threshold is needed. The checked theorem
`prod_gaussianReal_double_straddle_le` proves (11). `gaussPi_map_patchSample`
constructs the exact product law from four standard Gaussian coordinates;
`sum_twoVertexForms_sq` and `inner_twoVertexForms` check all port variances
and correlations. If `s+c^2 v=v` and `v+r=1`, Sheppard's bound and (10) give
`integral_twoVertexGaussianCost_le`:

```
E cost(t) <= acos(v-r)/pi + acos(cv)/pi + 2r/(pi^2 sqrt(sv)).  (12)
```

For the symmetric covariance suggested by the limiting cubic-tree wave, set

```
a=(1+2 sqrt(2))/4, b=(2+sqrt(2))/4,
v=(1+a)/2, r=(1-a)/2, c=b/v, s=v-b^2/v.
```

The two within-side correlations are `a`; all four cross-side correlations
are `b`. Here `sqrt(sv)=(1+2 sqrt(2))/8`. The bound in (12) becomes

```
B_pair = acos(a)/pi + acos(b)/pi
         + 2(3-2 sqrt(2))/(pi^2(1+2 sqrt(2)))
       = 0.2770916914606445... .
```

`exists_twoVertexTreeModel` verifies an explicit model with exactly this
covariance and the cost bound for every threshold. The rational certificate
`twoVertexTreeBound_le` proves `B_pair<=5559/20000=0.27795`, and
`twoVertexTreeBound_lt_two_mul_gaussianCoefficient` proves `B_pair<2p`,
where `p` is the existing Gaussian coefficient. Thus the local gain is proved,
not just sampled. The numerical difference is approximately `0.0036102458`
per modeled pair.

The local estimate alone does not give a universal supply coefficient. The
finite-kernel covariance estimates below depend on measured local gaps. The
subsequent large-gap/small-gap dichotomy, approximate probability estimate,
matching assembly, and simultaneous concentration now complete that transfer
in `MatchingSupply.lean`. The resulting gain now has an explicit rational
certificate and does not establish the quarter coefficient required for five. The full
parity-consistency cost remains a separate quantitative obligation.

The Boolean identity and density argument above are deductions in this work.
The pair-separation input is the existing formalization of Sheppard's Gaussian
angle bound; no claim of historical novelty is made for the local estimate.

## The pair objective really bounds graph cuts

The four colors in the pair calculation are thresholded **edge scores**. They
are not the colors of the four neighboring graph vertices. `Pair.lean` makes
the required comparison explicit: keep chosen internal edges intact, subdivide
every other edge, and fix each new midpoint to its edge-score color. Every
original crossing is paid for by at least one half-edge. Thus
`Multigraph.cutSize_le_portCut` bounds the original cut by the auxiliary energy.
`portCut_eq_blocks` regroups that energy exactly into singles and pairs, with
each external half-edge and each selected internal edge counted once. This
identity requires an actual vertex and edge partition; it does not count
overlapping patch energies as disjoint savings. Identifying a pair summand with
`twoVertexEnergy` additionally requires its selected internal edge to join the
designated vertices and its outer incidences to be the four recorded ports.
Those graph-placement facts are not consequences of the regrouping identity.

There is an explicit common choice of keys. For outer scores `a,b,c,d`, set

```
k_u = min(max(a,b), max(min(a,b),min(c,d))),
k_v = min(max(c,d), max(min(a,b),min(c,d))).
```

`PairLayout.twoVertexEnergy_pairKey` proves that these keys attain the pair
minimum at every threshold. Each selects an outer score. The Boolean theorem
`twoVertexCost_le_starCost` also proves the pair cost is no larger than the
two original straddling indicators, for every central-edge color.

`PairLayout.exists_key_of_portCut` supplies an injective ordering from a uniform
auxiliary-cost bound `B`: if original edge keys have multiplicity at most `T`,
each edge can supply at most `L` vertex keys, and degree is at most `d`, every
prefix cut is at most `B+dTL`. This is a deterministic transfer theorem; the
uniform cost and bounded-load hypotheses must still be established for the
chosen finite-graph random layout.

## Rigidity and stability of two critical-ratio stars

`Frontier/Layouts/KernelRigidity.lean` now supplies part of the covariance bridge.
Write the six vertex rows as `u,v,a,b,c,d`, with centers `u,v`. At every coordinate,
assume nonnegative `u` and that each of the five edge ratios is either `sqrt(2)`
or its reciprocal. Under the saturated equations

```
v+a+b = 2 sqrt(2) u,
u+c+d = 2 sqrt(2) v,
```

`exists_criticalStarAmplitude` proves there are just four possible coordinate
shapes, scaled by the `u` coordinate. Grouping the squared `u` coordinates by
shape gives weights. `criticalStarWeights_eq_of_unit` proves that unit row
variances force these weights to be `(1/3,1/3,1/6,1/6)`. Consequently the vertex
correlations are `2 sqrt(2)/3` on the five edges, `5/6` at distance two in this
two-star tree, and `sqrt(2)/2` at distance three. After normalization, the outer
edge correlations are exactly the `a,b` of the preceding Gaussian model.

This is also connected to the cost theorem: `gaussPi_map_forms_eq_of_gram`
proves equality of the full joint Gaussian law from equal Gram matrices, even
when the coordinate spaces differ. `integral_criticalStarPort_cost_le` then
proves the same bound `B_pair` for every threshold of any saturated realization.
It does not assume the particular independent-coordinate representation used
to derive the probability estimate.

There is a quantitative version. For six unit rows satisfying the exact edge
ratios, put

```
E = ||v+a+b-2 sqrt(2) u||_2^2 + ||u+c+d-2 sqrt(2) v||_2^2.
```

`criticalStarGram_stable` proves that every vertex covariance differs from its
symmetric value by at most `400 E`. The proof deletes coordinates outside the
four saturated shapes. A nonsaturated coordinate has a fixed squared gap, so
its `u` mass is at most four times its star defect. The discarded contribution
to any covariance is at most `16 E`; the remaining mixture has variance errors
at most `16 E`, and the checked weight inversion controls its covariance errors
by `384 E`. All constants are independent of the number of coordinates.

The preceding theorem has exact edge ratios. There is now also a checked
approximate version, including a bound on the error of finite kernels.

## From finite distance kernels to approximate covariance

For a ratio `q`, define

```
edgeRatioError(q,a,b) = min((a-qb)^2,(b-qa)^2).
kappa = 2q/(1+q^2), delta = D ((D-1)q^2)^R.
```

Here `D` bounds graph degree and `R` is the truncation radius. Assume
`1/2<=q<=1`, `delta<=1/4`, and that one adjacent pair of unit kernel rows has
correlation at most `kappa+eps`, with `eps>=0`.
`sum_unitKernel_edgeRatioError_le` in `KernelStability.lean` proves

```
sum_z edgeRatioError(q,unitKernel(u,z),unitKernel(v,z)) <= 48 eps+16 delta. (13)
```

This applies to the actual finite normalized kernel. At raw coordinates with
different adjacent distances, the ratio error is zero. Equal-distance
coordinates contribute positive correlation slack. Cutoff coordinates are
bounded by the truncation spheres. The existing correlation inequality and
Cauchy-Schwarz then control unequal row normalizers, giving (13).
Perturbing `q` to `q*=sqrt(2)/2` gives the checked bound

```
sum_z edgeRatioError(q*,unitKernel(u,z),unitKernel(v,z))
  <= 96 eps+32 delta+4(q*-q)^2.                              (14)
```

For the six rows of two adjacent stars, let `F` be the sum of the five
critical-ratio errors and `E` the two squared star residuals defined above.
`exists_criticalStarRows_near` constructs one common set of exact-ratio rows,
keeping the first center fixed, whose squared distance from each original row
is at most `12 F`. The construction rounds along the five-edge tree, so the
two stars use the same value at their shared center.

`criticalStarGram_stable_of_variances` allows the rounded rows to have imperfect
variances. `criticalStarGram_stable_approx` in `KernelCovariance.lean` combines
this with Cauchy-Schwarz and a star-residual perturbation estimate to prove

```
abs(covariance(i,j)-symmetricCovariance(i,j))
  <= 800 E+374700 F+50 sqrt(12 F).                          (15)
```

The constants are not optimized; their dimension independence and convergence
to zero are the useful properties. `unitKernel_criticalStarGram_le` applies
(15) directly to six graph vertices using (14), replacing `F` by
`5(96 eps+32 delta+4(q*-q)^2)` when the five relevant correlations satisfy the
upper bound. No exact-ratio, equal-normalizer, or girth assumption remains in
that finite-kernel theorem.

## The star gap controls the covariance hypotheses

`StarStability.lean` connects the measured residuals to the same star inequality
used by the existing Gaussian layout proof. Let `x` be a unit center and let
`y_0,y_1,y_2` be unit edge rows with `a_j=<y_j,x> >= kappa`, where
`1/2 <= kappa <= 1`. Write

```
G = ||y_0+y_1+y_2||^2 - 9 kappa^2 >= 0.
```

The checked inequalities include

```
3 sum_j (a_j-kappa) <= G,
||sum_j y_j - 3 kappa x||^2 <= G,
||sum_j (2 a_j y_j-x) - 3(2 kappa^2-1)x||^2 <= 16 G.
```

For a normalized sum of two unit kernel rows, `2 a_j y_j-x` is exactly
the neighboring vertex row. `edgeVector_reconstruct` verifies this identity.
Consequently every adjacent row correlation is at most
`2 kappa^2-1 + (4/3)G`, and moving the residual target to `2 sqrt(2)` costs only
twice the squared target discrepancy.

`unitKernel_criticalStarGram_le_of_gaps` in `KernelCovariance.lean` combines
these estimates with (14)--(15). If both edge-star gaps are at most `g`, and
`2 kappa^2-1 <= 2q/(1+q^2)`, it uses

```
E <= 64g + 4[3(2 kappa^2-1)-2 sqrt(2)]^2,
F <= 5[128g + 32 delta + 4(q*-q)^2].
```

The final covariance bound tends to zero with these quantities. Correlation
upper bounds and star residual bounds are no longer independent assumptions.
The theorem retains the explicit edge-star lower bounds, positive pair norms,
kernel truncation bound, and the two measured gaps.

## Large gaps improve a full ordering; small gaps supply many pairs

`StarSupply.lean` proves the uniform probability saving

```
Pr[v straddles threshold t] + G_v/(4 pi) <= straddleBound(rho).
```

Here `G_v` is the intrinsic edge-star gap, with `kappa^2=(1+rho)/2`.
The assumptions are the existing finite-kernel correlation lower bound and
`rho>=17/32`. The measured mean correlation is exactly
`(1+3rho)/4+G_v/6`. Jensen's inequality retains this extra term; the fact that
cosine is one-Lipschitz yields the displayed linear saving. The estimate holds
at every real threshold, including nonzero thresholds and degenerate stars.

The existing concentration proof now accepts any uniform total-mean estimate
through `exists_good_sample_of_mean`; the original theorem is its unchanged
specialization. `exists_good_sample_with_gap` applies the sharper mean to one
injective ordering. For `h=|V|`, its bound is

```
h max(9/(2T^2)+3eps,
      straddleBound(rho) - sum_v G_v/(4 pi h)
        + (9/2)(2T/M)/sqrt(2pi) + 4eps).
```

The explicit size hypothesis and the tail/window overhead are the original
ones. Thus a positive average gap gives a fixed improvement of the leading
layout coefficient in this regime, not merely a fixed-threshold improvement.

The complementary packing argument is checked in `Packing.lean`. A maximal
disjoint subfamily covers all eligible edges by conflict neighborhoods. In a
cubic simple graph each edge conflicts with at most five edges, including
itself. Removing a bad vertex discards at most three edges. For any nonnegative
gap function and `tau>0`, `exists_matching_small_gap` supplies a matching `P`
whose endpoints all have gap at most `tau`, satisfying

```
3 h tau <= 10 |P| tau + 6 sum_v G_v.
```

`gap_layout_or_small_gap_matching` combines the two branches: either one full
ordering has its mean coefficient reduced by `tau/(24pi)`, or there are at
least `h/5` disjoint eligible pairs with both endpoint gaps at most `tau`.
This uses the standard maximal-packing argument and makes no novelty claim
for that combinatorial principle.

The small-gap branch now has a uniform approximate Gaussian patch-cost
bound, explicit graph placements, a key-load bound, and concentration estimates,
described next. The completed threshold-grid and tail assembly keeps the same
ordering and accounts for ties. This proves a strict improvement, but does
not establish the target quarter coefficient; full redundant-parity
preservation remains a separate quantitative problem.

## Small covariance errors preserve the pair saving

`GaussianStability.lean` proves a dimension-independent, threshold-uniform
perturbation theorem. Fix four unit reference rows `b`. For every `eps>0`,
`exists_twoVertexThresholdCost_tolerance` supplies `delta>0` such that any four
unit rows `a`, in any finite coordinate space, satisfy

```
max_ij |<a_i,a_j>-<b_i,b_j>| < delta
  implies
E[cost(a,t)] <= E[cost(b,t)] + eps, for every real t.
```

The proof realizes both covariance matrices in four dimensions using their
positive semidefinite square roots. Continuity of those square roots gives a
coupling whose corresponding unit rows have correlation at least `rho`, with
`rho` arbitrarily close to one. Sheppard's all-threshold bound gives a mismatch
probability at most `acos(rho)/pi` for each corresponding port. The checked
Boolean inequality `twoVertexCost_le_add_disagreements` charges at most one per
changed port. Thus the error in the expected cost is at most
`4 acos(rho)/pi`, independently of the threshold. Equality of Gaussian laws
from equal Gram matrices transfers the estimate back to the original spaces.
The covariance matrices need not be invertible.

`exists_twoVertexTree_tolerance` specializes this to the tree model. Since
`B_pair<2p`, `exists_twoVertexTree_saving` gives fixed positive `delta,eta` such
that every sufficiently close realization has expected cost at most `2p-eta`
at every threshold. This qualitative theorem leaves the tolerance existential;
the quantitative construction below certifies a specific covariance radius. The matrix-square-root continuity and factorization are
Mathlib's `CFC.continuousOn_sqrt` and `CFC.sqrt_mul_sqrt_self`, applied with its
matrix order and operator norm instances. The coupling and cost transfer are
deductions here, with no historical novelty claim.

`KernelPairStability.lean` then handles the four *actual normalized outer edge
vectors*. Their covariance is a continuous function of the six vertex
covariances, with denominators positive at the critical model.
`exists_unitKernel_pair_tolerance` supplies a vertex-covariance tolerance for
the same expected-cost estimate. Finally,
`exists_unitKernel_pair_gap_tolerance` composes this with the checked
finite-kernel gap estimate. For each `eps>0` it chooses one `tau>0`, before
the finite graph, six vertices, radius, and threshold. In addition to the
previous kernel hypotheses, it is enough that both star gaps and each of

```
3 (2q^2)^R,
|sqrt(2)/2-q|,
|3(2 kappa^2-1)-2sqrt(2)|
```

are at most `tau`. The actual pair cost is then at most `B_pair+eps` at every
threshold. Taking `eps=(2p-B_pair)/2` retains a fixed positive saving.
`exists_pair_kernel_parameters` also chooses one graph-independent `q,R,rho`
that meets these approximation tolerances and the original kernel correlation
bound simultaneously, with `straddleBound(rho)<=p+xi` for any `xi>0`. The
compatible star parameter is `kappa=sqrt((1+rho)/2)`. Thus the original single
vertex estimate and the perturbed pair estimate can use the same Gaussian
scores. This closes the local probability and scalar parameter-selection steps
in the small-gap branch. The following results assemble the actual patches
and concentrate their combined cost at each fixed threshold.

## Actual matchings and a uniform saving in the mean

`PairGeometry.lean` constructs the six-row model around every actual edge of
a cubic graph. Its four outer edges have the correct incidences, and its two
local star gaps equal the intrinsic gaps at the endpoints. Neighbors across
the two stars may coincide: no girth assumption is used.
`exists_pair_estimate_parameters` chooses the gap tolerance before the
singleton accuracy, then chooses one set of finite-kernel parameters before
the graph. This order of quantifiers lets both branches use the same scores.

`MatchingLayout.lean` assembles every endpoint-disjoint matching into one
explicit real vertex key. At each threshold, its auxiliary cost is exactly
the sum of the singleton and pair minima, and bounds the original graph cut.
Every selected key is a nearby actual edge score. An edge can supply at most
18 keys in a subcubic graph; hence an edge-score tie bound of `T` gives a
vertex-key tie bound of `18T`. `exists_key_of_matchingCost` turns a uniform
cost bound `B` into one injective ordering with every prefix cut at most
`B+54T`. This includes prefixes that split a tie group.

In `MatchingMean.lean`, `exists_uniform_matching_mean_saving` proves the
following graph-independent statement:

```
There exist q, R, rho, eta with eta > 0 such that every finite cubic H
has a matching M and common vertex keys satisfying, for every real t,

  E[matchingCost(H,M,t)] <= |V(H)| (p-eta).
```

The theorem is named `Frontier.PairLayout.exists_uniform_matching_mean_saving`.
It retains the original kernel correlation hypotheses. If the total star gap
is large, the empty matching and the sharper singleton estimate give the
saving. Otherwise, the packing theorem supplies at least `h/5` disjoint
small-gap pairs, and their improved expectations add exactly. The matching
and its neighbor enumerations are chosen before the Gaussian sample and
threshold. The quantitative counterpart
`exists_uniform_matching_mean_explicit` certifies `eta=10^-48`.

`MatchingLocal.lean` then assigns each pair cost to its first endpoint and
zero to its second. Each vertex contributes at most two and depends only on
the radius-`R+2` ball. Two unit indicators per vertex express the total cost.
Applying the existing second-moment theorem yields, for each fixed `t` and
`c>0`,

```
Pr[|matchingCost(t)-E matchingCost(t)| >= c]
  <= 4 h vertexOverlap(3,R+2) / c^2.
```

This is `measureReal_matchingCost_deviation_le`. It does not assume that
overlapping patches are independent.

## A strict universal supply improvement

`MatchingGrid.lean` transfers every score-window or tail count to a vertex
count at cost at most 18 per source edge. A degree-three cut then pays at most
54 per source edge. `exists_key_of_matching_grid` proves one injective ordering
from the resulting finite grid estimates. Every intermediate prefix, including
one splitting a tie group, is included.

`MatchingGaussian.lean` chooses one sample controlling all `N` cost thresholds,
all `N` windows, and both tails. With `D=vertexOverlap(3,R+2)`, the union bound
is below one as soon as

```
(6N+3) D / eps^2 < h.
```

If the mean is at most `mu h`, the checked all-prefix bound per vertex is

```
max(81/T^2 + 54 eps,
    mu + 81 (2T/N)/sqrt(2pi) + 55 eps).
```

The constants are deliberately coarse; all window, tail, and tie costs
vanish within any fixed positive saving. Cap the mean saving at `eta<=1/100`,
take `T=100`, `eps=eta/220`, and `N=ceil(32400/eta)+1`. Lean verifies that the
displayed bound is at most `p-eta/2`. Thus
`Frontier.PairLayout.exists_cubicLayoutBound_lt_gaussian` proves

```
exists p' > 0, p' < p and CubicLayoutBound(p').
```

`MatchingSupply.lean` applies the existing compression theorem to obtain
`LayoutBound(3,2p')`, then the existing frontier lower-bound theorem. Its
principal declaration, `Frontier.exists_lowerBound_gt_gaussian`, supplies a
single constant

```
L' > 1 + 1/(2p) = 4.5624976789...
```

such that every dense rectangle-free family satisfying the original
subexponential-threshold hypotheses requires more than `(L'-eps)n` binary
gates for every fixed `eps>0` and sufficiently large `n`. The alphabet is any
finite nontrivial alphabet; the circuit basis and interpretation are unrestricted.
The theorem counts positive-arity gates, as does the existing lower bound.

This is a universal asymptotic theorem, not a finite experiment or a conditional
layout hypothesis. The quantitative continuation below supplies an explicit
value of `L'`. The quarter supply theorem and preservation under an arbitrary
linear number of free redundant parity inputs remain open. The local
Gaussian, concentration, and compiler results it composes are credited in the
preceding sections; no claim of historical priority is made.

## An explicit numerical certificate

[`GaussianQuantitative.lean`](../../Frontier/Layouts/GaussianQuantitative.lean)
replaces square-root continuity with an explicit positive-semidefinite coupling.
The four-port reference covariance `B` satisfies `B >= (1/25) I`. If
`max_ij |A_ij-B_ij| <= delta`, then

```
|x^T (A-B) x| <= 4 delta ||x||^2.
```

Consequently `A-c^2 B` is positive semidefinite whenever
`4 delta <= (1-c^2)/25`. Couple the perturbed ports as `c` times the reference
ports plus independent Gaussian noise with covariance `A-c^2 B`. Each port
pair then has correlation exactly `c`, so the same all-threshold disagreement
argument costs at most `4 acos(c)/pi`. This uses Mathlib's matrix square-root
factorization; the quantitative coupling is a deduction here.

The checked constants, intentionally conservative, are:

| Quantity | Certified value |
| --- | --- |
| Four-port covariance tolerance | `10^-14` |
| Coupling correlation | `1-10^-10` |
| Expected pair-cost error | at most `1/5000` |
| Six-vertex covariance tolerance | `10^-16` |
| Normalization error factor | at most `28` |
| Star-gap and kernel-error tolerance `tau` | `10^-44` |
| Pair saving relative to `2p` | at least `1/2000` |
| Uniform mean saving `eta` | `10^-48` |
| Cubic layout saving | `eta/2` |
| Cycle-rank supply saving | `eta` |

The local model bound `B_pair <= 5559/20000` and `2p >= 279/1000` leave enough
room for the stated pair error and saving. The finite-kernel covariance estimate
is at most `10^-16` at this `tau`. The matching dichotomy requires only
`10 eta <= 1/2000` and `2 eta <= tau/(24 pi)`, both checked exactly. The existing
concentration and grid estimates consume half the mean saving; compression
then doubles the cubic coefficient.

[`MatchingSupply.lean`](../../Frontier/Layouts/MatchingSupply.lean) therefore proves

```
A_* = 2p - 10^-48,
L_* = 1 + 1/A_*,
LayoutBound(3,A_*),
L_* >= L_0 + 10^-47,
s > (L_* - epsilon)n for every fixed epsilon > 0 and sufficiently large n.
```

These are `layoutBound_matching_explicit`, `matchingCircuitCoefficient_gain`,
and `lowerBound_matching_explicit`. No unproved supply hypothesis remains in
their statements. The old coefficient is `L_0=1+1/(2p)`. A separate high-precision
evaluation gives `L_*-L_0` approximately `1.2691389712346145 * 10^-47`; this decimal
is a display calculation, while Lean verifies the exact formulas and rational
lower bound. The first usual decimal digits of `4.56249767892501858...` do not
change.

The asymptotic coefficient is explicit. The kernel radius and eventual graph
and input-size thresholds are still existential. The square-root dependence
in the existing covariance estimate, together with conservative tolerances,
accounts for the very small certified gain; no optimality is claimed.

## Free parity inputs: the exact preservation question

The proposed strong theorem concerns a binary circuit `C` receiving

```
(x,Px),  x in F_2^n,
C(x,Px)=f(x) for every x.
```

The parity map is free, and correctness away from this linear code is not
required. The desired conclusion is `size(C)>=L n-o(n)` even for a linear
number of redundant supplied inputs. It is not a consequence of invariance
under an invertible basis change.

The following preservation results are now checked in `Frontier/Parity.lean`:

- `ncard_inputGraph`: the consistent accepting set has cardinality `|S|`.
- `SumsetFree.inputGraph`: it is `K`-sumset-free whenever `S` is. For a sumset
  contained in the graph, fix an element on one side. Projection onto original
  inputs is injective on the other side, by cancellation of the supplied
  coordinates. Both projected sides therefore have their original sizes.
- `AdditiveSweep.ncard_le_inputGraph`: any additive sweep that actually enforces
  this promise has the same demand `|S| <= (K-1)^2 transitionCount`.
- `lowerBound_sumsetDisperser_freeBasis`: when the supplied input coordinates
  form an invertible additive basis, the full circuit coefficient is preserved.
  Transform the target by the inverse basis; dispersion and density are unchanged.
- `ncard_le_parity_sweep`: start with any nested sweep of an ambient accepting set
  that agrees with the hard set only on consistent inputs `(x,Lx)`. Adding a
  partial syndrome yields the checked finite inequality
  `|S| <= (K-1)^2 q^k transitionCount`, where `k` is the number of supplied
  coordinates. The original independent input count is retained in `|S|`.
- `ncard_le_parity_joint_codes`: for the same promise-only correctness model,
  replace the separate syndrome factor by a joint rank at each transition.
  If `E:x |-> (x,Lx)` and `C_t` encodes the other required values, the bound is
  `|S| <= (K-1)^2 sum_t |C_t| q^(rank E_(P_t union Q_t) +
  rank E_(P_t^c union Q_t) - n)`. The code and visible values must determine the
  original complete transition on consistent accepting inputs.

These statements use `Sweep.restrictHom` from
`Frontier/Boundary/Syndrome.lean`. For an arbitrary additive promise `Rz=a`, equal
old syndromes and equal original transitions determine the new syndrome. The
checked general bounds `transitionCount_restrictHom_le` and
`transitionCount_restrictLinear_le` therefore pay `|range R|`, or `q^(rank R)`,
once. This is a construction of a sound sweep, not just a hardness assertion for
the graph of the supplied values. It does not remove the syndrome factor when
the number of redundant supplied parities is linear.

The graph lemma holds even for nonlinear supplied values. This highlights its
scope: if one supplied `f(x)` itself, the promised circuit could simply read it,
despite preservation of graph hardness. A supply proof must use the linearity
of the added values and retain consistency under splicing.

For redundant parities the existing [additive compiler](additive.md) and
[joint-rank code](joint.md) give a precise starting point. Let the `m` reached
affine input forms have rank `d`, and put `c=m-d`. Sumset hardness gives
`d=n-o(n)`. The separate-syndrome bound gives, in the linear-size regime,

```
n <= A(s-m)^+ + c + o(n),
s >= L n-(L-2)c-o(n).                                       (8)
```

The possible `s-m=-1` changes only an additive constant. The underlying circuit
is connected and reads at most `s+1` inputs. In particular, sublinearly many
redundant reached forms preserve the leading coefficient. The existing checked
aggregate-gate theorem separately covers sublinearly many supplied parities
by including their parity computations as special gates.

Equation (8) is now formalized directly for free supplied linear inputs, without
building gates for the supplied forms. `Frontier/Parity/LowerBound.lean` proves
`lowerBound_linear_inputs`: for every proved layout coefficient `0 < A <= 1`,
every sufficiently large independent input length, every number of supplied
inputs, every linear input map, and every binary circuit correct on that map's
image,

```
(1 + 1/A - epsilon)n < s + (1/A - 1)c.
```

The hypotheses on the target are sumset-freeness, `log K=o(n)`, and density
`log_q |S|=n-o(n)`. The statement imposes no condition on inconsistent supplied
inputs. It counts positive-arity gates and allows an arbitrary signature and
interpretation over a finite field. The existing Gaussian layout theorem, as
well as the strict improved coefficient, supplies the layout premise.

The checked reduction makes each loss explicit:

- `Parity/Support.lean` proves `q^(n-d)<K` for the actual read observation map.
  It also proves that deleting unused coordinates cannot increase redundancy.
- `Parity/Image.lean` proves that a saturated additive image remains sumset-free.
  The summand sets may lie outside the image subspace: the proof first translates
  them in opposite directions, then lifts them. Each observation fiber has at
  most `q^(n-d)` original inputs.
- `Network/Read.lean` removes unread inputs without changing the graph or its
  acceptance on the remaining inputs. `Parity/Network.lean` then imposes the
  quotient syndrome of the read code, whose dimension is exactly `c=m-d`.
  Its finite bound is
  `|S| <= q^(n-d)(K-1)^2 q^c (|V| q^(w+degree+readsPerVertex) + 1)`.
- `Parity/Reduction.lean` proves both
  `cycleRank+c <= s-n+log_q K+1` and
  `log_q |S| <= w+c+3log_q K+log_q(|V|+1)+4` for binary circuits.

`lowerBound_linear_inputs_of_sublinear_redundancy` absorbs `c=o(n)` and recovers
the entire coefficient. `lowerBound_linear_inputs_of_sublinear_codimension`
gives the same conclusion when the total supplied code has sublinear
codimension. Thus `o(n)` free extra parities are covered in the promise model
itself. Neither theorem asserts preservation for arbitrary linear redundancy;
the explicit `(L-2)c` loss is exactly what the full target must remove.

There is also a checked numerical linear-rate result. Combining the weighted
reduction with the explicit matching supply improvement,
[`Parity/Matching.lean`](../../Frontier/Parity/Matching.lean) proves
`linear_redundancy_rate_preserving_gaussian_explicit` and
`free_parity_rate_preserving_gaussian_explicit` with

```
gamma = 10^-48.
```

Apply the improved weighted theorem with `epsilon=gamma`. Lean verifies
`L_*-L_0 >= 10 gamma` and `L_*-2 <= 9`. If the read redundancy is at most
`gamma n`, its loss is at most `9 gamma n`, leaving `s>L_0 n` for all
sufficiently large `n`. The rate is chosen before the finite field, hard
sumset-free family, or supplied linear map.

The parity theorem specializes this exactly to circuits receiving `(x,Lx)`
for free with at most `gamma n` extra parities and correctness required only
on those pairs. Deleting unread supplied coordinates cannot increase code
redundancy, so the number of extra parity inputs bounds the read redundancy.
The theorem measures size against the original `n` independent input bits.
The earlier existential declarations remain as corollaries.

This preserves the full old coefficient at the stated numerical rate. It does
not preserve the full improved coefficient at a positive rate or cover an
arbitrary linear number of parities. In particular, it cannot yet remove an
arbitrarily large affine prefix for free.

At an individual transition, with read input indices `P`, unread indices `F`,
and visible affine inputs `Q`, the sharper exponent is

```
J = |B|-|Q| + rank L_(P union Q) + rank L_(F union Q) - d,     (9)
```

where `B` contains all distinct visible signals. It charges visible input values
and the consistency syndrome jointly. The same ordering must control both.
Compared with `A(s-n)`, the separate bound has an overhead
`(1-A)c = 0.7192980627...c`. Proving full parity preservation requires eliminating
this overhead, or using another representation/restriction argument.
The core count (5) also uses `m`, the number of reached supplied forms, in place
of `r`; replacing that number by their rank without a proof would lose this
same distinction between physical inputs and independent inputs.

The exact observation count in (9) is now checked, rather than assumed from the
abstract row-space identity: `LinearBoundary.ker_jointObservation` constructs
the two kernel summands, and `finrank_jointObservation` and
`ncard_jointObservation` prove the rank and cardinality formulas.
`Sweep.transitionCount_restrictLinear_le_joint` bounds complete transitions of
the consistency-enforcing sweep by this code and any supplied code for the
remaining information. It accepts singular input maps and redundant check
equations whenever `ker R=range L`. The parity specialization above proves
`rank E=n`; it does not replace the physical input count in a graph layout by
that rank. The common-ordering bound remains unproved.

If full preservation is established, a prefix of `ell` affine gates can be
replaced by free supplied parities (including every original-input bypass).
The remaining circuit would still need `L n-o(n)` gates, yielding
`s>=ell+L n-o(n)`. Prefixes with `ell>=(5-L)n` would then reach five. This
consequence remains conditional on the stronger redundant-input theorem.

## Validation and source boundaries

A build of all 116 library modules with `--wfail` passed all 3,960 jobs. The
axiom audit `lake env lean scripts/Audit.lean` passed with the new declarations
using only `propext`, `Classical.choice`, and `Quot.sound`. The worked compiler
and closure examples also passed. The earlier algorithm and communication
checks, including 1,024 independent affine observation profiles and the
critical-transition checks below, were unchanged by this numerical extraction.

The earlier Docker Comparator self-tests and clean candidate build passed.
That comparison stopped at its exact-coverage gate: the pinned reference
contained 916 public declarations and that candidate had 993, with 77 additions
and no missing declarations. A fresh native inventory after the joint-observation,
patch optimization, Gaussian pairs, finite-kernel stability, pair layouts,
star-gap supply, Gaussian perturbation, matching assembly, simultaneous
concentration, the improved circuit theorem, the read-restricted parity reduction,
positive-rate parity preservation, quantitative covariance coupling, explicit
supply and parity constants, and closure expansion contains 1,348 public
declarations: 432 additions relative to that reference, with none missing,
and 2,434 total theorem roots. It also retains all 1,300 public declarations
from the preceding native inventory.
This inventory is not a Comparator replay.
The pinned policy was left unchanged, and full Comparator proof replay is not
reported as passing for this work.

Run `python3 research/communication/critical_supply.py`; its saved output is
`critical_supply_results.json`. It checks:

- 2,805 exact integer-power fractional projection inequalities;
- the shared-selector overcount and parity obstructions for block budgets 1–6;
- 2,618 transition-product identities and 60 critical-cut equalities in compiled
  circuit sweeps;
- sound rank-plus-nonlinear certificates in those sweeps;
- 36 compressed cores and 864 cuts, including 640 exact forest-rank identities;
- 648 exact rational instances of the reflected-score obstruction.

Inputs are exhaustively enumerated, but circuits and layouts are sampled and
are not claimed to be minimal. Floating-point linear programming only proposes
weights; rational feasibility and the cardinality certificate are checked
exactly. These experiments establish no universal coefficient or layout gain.

The demand and cubic compression mechanisms come from the existing frontier
development; the supply refinements and obstruction proofs above are deductions
in this investigation. Fractional projection bounds are credited above. The
syndrome viewpoint follows the code-trellis literature, including Navin Kashyap,
[Matroid Pathwidth and Code Trellis Complexity](https://arxiv.org/abs/0705.1384).
The XOR-layered circuit model also predates this investigation: the
[Ryan Williams's notes on gate elimination](https://people.csail.mit.edu/rrw/cs294-2018/gate-elimination.pdf)
present the Demenkov–Kulikov argument with a measure charging both the upper
gates and the supplied affine forms. That result does not make linearly many
supplied forms costless in the full frontier coefficient.
