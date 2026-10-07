# Graph layouts and coherent decompositions

[Synthesis](../index.md) · [Existing join analysis](../../lower-bound-vantages/structural/joins.md)

**Verdict:** families 236 and 174 offer mechanisms to study, but their stated
conclusions do not improve the unrestricted frontier coefficient. The critical
Ising cut is quantitatively too expensive; thinness controls the wrong edges.
These are transfer obstructions, not claims that either source theorem is false.
The smallest useful next target is a uniform gain for the existing Gaussian
ordering, or a direct bound on the joint merge parameter.

## The exact resource and current baseline

For connected subcubic loopless networks, write `beta1=|E|-|V|+1`.
The binary compiler pays `beta1≈s-n` for `s` positive-arity gates and `n` read
inputs. A useful supply theorem must cover **every** compiled network, with
parallel edges counted individually. A linear layout needs

```
max_prefix |delta_G(prefix)| <= B beta1 + o(|V|),  B < A,
A = (3/pi) acos((1+2sqrt(2))/4) = 0.280701937272...
```

It would give `s >= (1+1/B)n-o(n)` under the existing demand hypotheses;
`B=1/4` would give five. The current coefficient is `4.562497678925...`.
This is an upper bound on a maximum over one coherent ordering, not an expected
cut, a selected separator, or an existence statement for a graph family.
[frontier][frontier]

The local Gaussian construction has the relevant quantifiers already:
finite-radius kernel rows on **all** simple cubic graphs, correlated edge
scores, vertex medians, threshold-grid concentration, and window/tail control.
Compression transfers the cubic coefficient `A/2` per vertex to `A` per cycle
rank. Inspect [Gaussian.lean](../../../Frontier/Layouts/Gaussian.lean) and the
paper's sections “Median layouts” and “Gaussian edge scores.” The tree-limit
straddling calculation is sharp for that score family; the paper explicitly
does not claim optimality of cutwidth or of all score processes.
[frontier][frontier]

## Family 236: an equivariant spin law is not a layout

**Source claim.** The free zero-field Ising law on the infinite `d`-regular
tree is FIID exactly when `theta=tanh(b) <= 1/sqrt(d-1)`, including equality.
The construction recovers observations from shared Brownian innovations by
comparing conditionally independent copies, then recovers the spins. Its
parameter `b` is inverse temperature, distinct from our cycle rank `beta1`.
The TeX introduction explicitly excludes finitary coding, coding-radius bounds,
parameter-uniform bounds, and computational bounds. [oai236][oai236]

**Inspected formal statement.** `docs/236.md`, `FreeIsing.json`,
`OAI/Probability/FreeIsing/Model.lean`, and `Main.lean` agree on a measurable
factor with the exact connected-subtree cylinder law. Equivariance is almost
sure for each fixed automorphism. The paper additionally claims an everywhere
equivariant version; that strengthening is not the comparator endpoint.
The actual endpoint is `OAI.Problem367.free_ising_factor_iff_threshold`.
It is a proof-bearing OAI declaration, inspected here but not recompiled.
[oai236][oai236]

**Our quantitative deduction.** A neighboring spin pair disagrees with
probability `p=(1-theta)/2`. For a connected cubic graph with `h` vertices,
`|E|=3h/2`, `beta1=h/2+1`, and `|E|/beta1 -> 3`. Even granting a perfect finite
transfer of the critical tree edge marginals, its mean-cut coefficient would be

```
p = (1-1/sqrt(2))/2 = 0.146446609407...
B_Ising = 3p = 0.439339828220... > A.
```

Any temperature in the stated FIID range has at least this disagreement rate.
Beating `A` through this one-spin mean cut would require
`theta > 1-2A/3 = 0.812865375152...`, outside the range `theta<=0.70710678...`.
The `h`-normalization is `3p/2`, not `p`: confusing them reverses the comparison.
These calculations do not assert a finite-graph Ising theorem.

There are two further missing bridges. First, two spin values give a bipartition
with macroscopic ties, not nested cuts at all thresholds. Sorting independently
inside the classes introduces new cuts for which the source gives no bound.
Second, measurability on an infinite tree supplies no stated finite-radius
error estimate valid on arbitrary short-cycle cubic graphs. Qualitative local
approximation on the tree alone does not provide that uniform transfer.

The source's concentration concerns the particular path observables needed to
recover its factor. It is not a bound on the maximum finite-graph frontier.
The useful reusable idea is joint coupling with a common innovation source;
any proposed real-valued key process must still prove the missing marginal,
dependence, finite-graph, and simultaneous-threshold estimates.
[oai236][oai236]

## Local median gains: a precise test of the attempted repair

The repository already proves that replacing an independent set of vertices'
keys by the medians of their neighbors' original keys improves every threshold
cut. `Multigraph.cutSize_eq_add_gain` adds the selected star gains exactly;
`LocalLayout.cutSize_improve_cubic_le` supplies the simultaneous inequality.
These are in [Local.lean](../../../Frontier/Layouts/Local.lean).
No positive uniform expected gain is part of those conclusions.
[frontier][frontier]

**Our deduction under the free-tree star law.** Condition on the central spin.
Its number of disagreeing neighbors is `K~Binomial(3,p)`. A majority update
saves `g(K)=max(0,2K-3)`, so

```
E g(K) = 3p^2(1-p) + 3p^3 = 3p^2.
```

For any one independent update set, even one chosen from the spins, the total
gain is at most the sum of these nonnegative gains over **all** vertices.
Consequently, under exact critical tree star marginals, the normalized
mean-cut proxy after that pass is bounded **below** by

```
3p - 6p^2 = 0.310660171780... > A.
```

This excludes a better mean-cut estimate from that one-pass critical-Ising
repair, even before ordering and finite-graph transfer. It does not exclude
rare good cuts, repeated passes, another temperature, or other score processes.
A spin-independent set of density `1/4` gives the weaker proxy
`3p-(3/2)p^2=0.407169914110...`. Both are exact star-law deductions, not
new finite-graph layout bounds. The checker enumerates all eight star patterns.

For the existing Gaussian keys, the appropriate open theorem is: there is
`epsilon>0` and a rule valid on every sufficiently large cubic graph that gives
a linear expected gain at the thresholds controlling the maximum, enough to
lower the final per-vertex bound below `A/2`. The proof must retain simultaneous
concentration, window/tail control, and bounded tie-breaking cost. A gain only
at zero on the infinite cubic tree is insufficient. [frontier][frontier]

## Family 174: all-cut thinness has the wrong direction

**Source claims and inspected endpoints.** For every finite loopless
`k`-edge-connected multigraph, a spanning tree satisfies
`|delta_T(S)| <= (C/k)|delta_G(S)|` for every nontrivial cut, for one absolute
`C`. A companion gives a deterministic polynomial-bit construction, including
binary-encoded multiplicities. These are separate existential and algorithmic
claims; neither specifies a useful numerical `C`. [oai174][oai174]
[oai174algorithm][oai174algorithm]

`StrongThinTree.json` selects `OAI.Combinatorics.ThinTrees.Main`; its proof
chooses `C := 3 * max C0 1`, hence `C>=3`. Every connected subcubic graph has
`k<=3`, so this witness has `C/k>=1`: the thinness inequality is already true
for every spanning tree because `T` is a subset of `G`. This is a direct
inspection of the chosen witness, not a claim that the best possible constant
must be at least three. The algorithmic endpoint in
`ThinTrees/Encoding/AlgorithmicMain.lean` asserts a fixed machine, polynomial
fuel in encoded input length, and a valid tree output. [oai174][oai174]
[oai174algorithm][oai174algorithm]

**Our scalable counterexample to the naive transfer.** In the cubic prism
`C_m square K_2`, take a Hamiltonian path that traverses one layer, crosses one
rung, then traverses the other layer. It is a spanning tree and satisfies
the stated inequality with `C=k=3`. The cut separating the layers crosses
one tree edge but `m` original edges. Thus thin tree cuts cannot be substituted
for original-network boundaries. The checker exhausts every nontrivial cut
for `m=3,...,7`; the displayed construction proves the discrepancy for all
`m>=3`. The prism itself has good layouts: this example refutes the implication
from that tree's thinness to low routed congestion, not their existence.

Duplicating each edge `q` times multiplies both connectivity and cut size by
`q`, leaving `(C/k)|delta_G(S)|` unchanged. High connectivity obtained this way
does not repair the coefficient. A substantive transfer would need a new
selection/routing theorem controlling **original** edges across a coherent
decomposition, with constants charged against the original cycle rank.

## The branching target is joint merge width

For disjoint child regions `W1,W2`, with `W=W1 union W2`, the actual merge cost is

```
j_G(W1,W2) = |delta_G(W1) union delta_G(W2)|
           = (|delta_G(W1)|+|delta_G(W2)|+|delta_G(W)|)/2.
```

A triangle has all three individual boundaries of size two and joint cost
three. Applying thinness to all three only gives `j_T <= (C/k)j_G`, still the
wrong direction. With leaf costs included, the existing
[join analysis](../../lower-bound-vantages/structural/joins.md) identifies the
minimum budget with `tw(L(G))+1`, by Harvey and Wood's congestion theorem.
The multigraph extension and support transfer are paper deductions there;
the checked weighted network theorem additionally requires unique traces and
accounts for local reads. [harveywood18][harveywood18] [frontier][frontier]

The exact sufficient open bridge is `tw(L(G))+1 <= B beta1+o(|V|)` with `B<A`
for every compiled connected subcubic network. The source's nested packing
hierarchy does not assert this bound or bound its original-edge merge loads.
For an algorithm, construction and local processing costs must also be controlled.

## Comparison screens and bounded next work

| Family | Inspected claim and model | Decision for this resource |
|---|---|---|
| 089 | Constant-distortion real `L1` embeddings of planar metrics; `C(k)` for graphs with bags of size at most `k`, independent of positive edge lengths. OAI endpoints inspected. [oai089][oai089] [oai089tw][oai089tw] | Restricted graph classes, unspecified constants, and weighted cut combinations. Even the isometric `L1` representation of `C4` uses two crossing cuts; these cannot both be prefixes or edges of one laminar decomposition. No general compiled-graph coverage or compatible-order theorem follows. |
| 102 | Optimal Max-Cut approximation hardness above the Goemans–Williamson constant; binary polynomial reductions to simple unweighted graphs. The paper's rounding probability is `acos(rho)/pi`. OAI endpoint inspected. [oai102][oai102] | This controls one maximization objective, not minimum maximum frontier. The local Gaussian proof already uses that angle identity at every threshold. The hardness ratio supplies no new layout coefficient. |
| 178 | Deterministic full adjacency-list construction of nonbipartite Ramanujan graphs for every fixed degree and sufficiently large even order; degree-dependent polynomial time. Paper screen only. [oai178][oai178] | Useful adversarial test families, not universal supply. In degree three, the spectral gap alone gives bisection lower bound `(3-2sqrt(2))h/4`, or `0.08578644 beta1` asymptotically, far below `A`; it is a lower bound, not a layout construction. |
| 175/176 | Integral/fractional expectation-threshold comparison and random-graph containment bounds. Introductions and scope docs inspected. [oai175][oai175] [oai176][oai176] | Explicitly deferred. Random containment does not cover every deterministic compiled graph. Copies or cut embeddings chosen separately can be incompatible across transitions; no common routing/order or cycle-rank accounting is supplied. |

**Smallest tests and stopping rules.** First run the eight-state star calculation:
it already rejects the direct critical-Ising and one-pass mean-cut proposals.
Reject thin-tree-only transfers on the six-vertex prism before implementing an
algorithm. Reject automatic cut-family-to-order conversion on `C4`. For a new
Gaussian rule, test finite-radius star neighborhoods with short cycles as well
as the tree, and charge windows and ties. Stop a candidate if any required
uniform gain fails; a finite success authorizes a proof attempt, not a coefficient.
For a new decomposition rule, compute its original joint boundaries and compare
with the existing exact finite [join checker](../../lower-bound-vantages/data/check_layout_identity.py).

## Validation and limitations

Run `python3 research/openai-math/structure/data/check_structure.py` from the
repository root; compare with [expected.txt](data/expected.txt).
The [stdlib checker](data/check_structure.py) verifies the constants, star gains,
21,814 prism cuts, the crossing `L1` cut representation, and the triangle join.
No simulation, asymptotic graph enumeration, or upstream theorem verification is
hidden in these checks. Sources are the pinned OpenAI commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a` and the local baseline named at the root.
Upstream Lean is `v4.34.1`, with Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`;
Frontier uses `v4.35.0-rc3` and a different Mathlib pin. Comparator `.lean` files
are intentional `sorry` targets; their JSONs select the OAI solutions and permit
`propext`, `Quot.sound`, and `Classical.choice`. Reading them is not running the
comparator or an axiom audit. No upstream build or import was performed.

[frontier]: ../sources.md#frontier
[oai236]: ../sources.md#oai236
[oai174]: ../sources.md#oai174
[oai174algorithm]: ../sources.md#oai174algorithm
[harveywood18]: ../sources.md#harveywood18
[oai089]: ../sources.md#oai089
[oai089tw]: ../sources.md#oai089tw
[oai102]: ../sources.md#oai102
[oai178]: ../sources.md#oai178
[oai175]: ../sources.md#oai175
[oai176]: ../sources.md#oai176
