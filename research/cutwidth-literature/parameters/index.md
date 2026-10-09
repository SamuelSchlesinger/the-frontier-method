# Related widths, conversion constants, and complete-transition capacity

[Review overview](../index.md) · [Search and access log](data/search-log.md) ·
[Finite checks](data/validate_conversions.py) · [Expected output](data/validation-output.txt)

The useful alternatives are **subcubic pathwidth**, **line-graph treewidth**, and
**joint signal/code capacity**. Published conversions preserve the leading constant
for the first, identify the correct merge objective for the second, and give exact
state formulas for the third. None of the sources checked here supplies a new
universal coefficient below the repository's `p h` cubic bound.

The baseline and application requirements are taken from the current
[README](../../../README.md), [RESEARCH](../../../RESEARCH.md), and
[joint-code note](../../communication/joint.md), not inferred from width terminology.
Here `pw` and `tw` use maximum bag size minus one; graph cutwidth counts edges with
multiplicity. Imported graph equalities below are stated for **simple graphs** unless
explicitly indicated. Cubic-core results still need the repository's multigraph restoration.

## What is ordered, and what is charged?

| Parameter | Decomposition objects | Cost of a cut or step | Relevance |
|---|---|---|---|
| Cutwidth | Vertex order | Edges between prefix and suffix | Existing wire supply |
| Pathwidth / vertex separation | Vertex order or path bags | Prefix vertices with a suffix neighbour | Same leading coefficient as cutwidth in subcubic graphs |
| Linear-width | Edge order | Vertices incident with an edge on both sides | Different order domain; close to pathwidth under stated hypotheses |
| Graph branchwidth | Tree with graph edges at leaves | Middle vertices of an edge partition | Does not directly count wire boundaries |
| Carving width | Tree with graph vertices at leaves | Graph edges crossing a tree-edge cut | Individual region boundary, not joint merge cost |
| `tw(L(G))+1` | Vertex embedding in a subcubic tree | Edges whose routes pass through one tree node | Exact graph objective for joint boundaries |
| Matroid pathwidth | Order of ground-set elements | `r(P)+r(S)-r(E)` | Linear-code state dimension, using the convention without `+1` |
| Signal hypergraph width | Order/tree of network vertices | Signals with occurrences on both sides | Can save repeated wires if occurrence connectivity holds |

Definitions and conversions are sourced in the sections below. An edge order of
`G`, a vertex order of `L(G)`, and a vertex order of `G` must not be silently identified.

## Graph searching gives a constant-preserving pathwidth route

Kinnersley proves equality of vertex separation and pathwidth [kinnersley92][kinnersley92].
For any fixed vertex order, each active prefix vertex owns at least one crossing
edge, and at most `Delta` crossing edges. Consequently the elementary bounds are
`pw(G) <= cw(G) <= Delta pw(G)`; the upper bound uses an order minimizing vertex
separation. The following sharper subcubic conversion is substantially more useful.

Golovach proves `cw(G)=pw(L(G))` for connected subcubic graphs with more than one
edge [golovach93][golovach93]. Harvey and Wood reproduce the general inequality
`pw(L(G))-floor(Delta/2)+1 <= cw(G) <= pw(L(G))` for `Delta>=2`
[harveywood18][harveywood18]. Fomin's Section 4, Lemma 6, uses graph searching to give
`pw(L(G)) <= pw(G)+2` for subcubic graphs [fomin03][fomin03]. Thus

```text
pw(G) <= cw(G) <= pw(G)+2                  (simple subcubic G).
```

**Consequence for this project:** any universal cubic pathwidth bound
`(c+o(1))h` transfers to cutwidth with the same coefficient `c`. At `c=1/8`, the
repository's existing cubic compression would supply `A=1/4` and the `5n` target.
This is a transfer, not a newly proved pathwidth estimate. See
[classical bounds](../classical/index.md) for the numerical literature.

The stronger assertion `cw(G)=pw(G)+1` is false: the finite checker obtains
`pw(K3,3)=3`, `cw(K3,3)=5`, and `pw(L(K3,3))=5`. The one-edge graph also needs care:
`cw(K2)=1` while `pw(L(K2))=0`. These are independently computed examples.

For minimum degree at least two, Fomin's Section 5 records
`pw(G) <= lw(G) <= pw(G)+1`, where `lw` orders **edges** and counts incident
vertices meeting both edge sides [fomin03][fomin03]. Hence a cubic linear-width
improvement also transfers with only an additive constant. Leaf and search-game
conventions matter: node searching, edge searching, and mixed searching are not
interchangeable definitions. They are valuable equivalent formulations for finding
an order; their names alone do not supply a better coefficient.

## Trees: optimize congestion at a merge, not just its three cuts

Seymour and Thomas's carving decompositions put vertices at tree leaves and charge
crossing graph edges. Their ratcatcher method computes weighted carving width for
planar graphs, and treats graph/hypergraph branchwidth through different middle-set
objects [seymourthomas94][seymourthomas94]. Arbitrary compiled circuits need not be
planar. Also, singleton leaf cuts are present in carving width: converting a vertex
order to a caterpillar gives width at most `max(cw(G),Delta)`, not always `cw(G)`.

Here is a direct accounting identity. At an internal node of a leaf-labelled
subcubic tree, let `A,B,C` be the three vertex parts. Every graph edge joining two
parts belongs to exactly two of their cut boundaries. Therefore

```text
J(A,B,C) := |delta(A) union delta(B) union delta(C)|
          = (|delta(A)|+|delta(B)|+|delta(C)|)/2 <= 3k/2
```

when the three cuts have size at most `k`. This proof counts parallel edges too.
The checker tests all 729 tripartitions of a six-vertex multigraph. It is a check
of the formula, not a substitute for the preceding elementary proof.

Harvey and Wood's Theorem 2.4 identifies minimum vertex congestion with
`tw(L(G))+1`: route every graph edge between its endpoint leaves and count routes
through tree nodes. Their Theorem 2.6 gives the corresponding path identity with
`pw(L(G))+1` [harveywood18][harveywood18]. At an internal node, that congestion is
exactly `J`. Thus **line-graph treewidth already measures the joint edge union**;
one need not first bound each separator and lose a factor `3/2`.

**Candidate, not a completed transfer:** prove a universal bound on this congestion,
then restore the compressed graph while charging locally read inputs and all merge
records in `TreeFrontier`. A cubic bound `(c+o(1))h` with `c<p` would be numerically
promising. If only carving width `(c+o(1))h` is available, the elementary sufficient
threshold is `c<2p/3`, approximately `0.0935673`; equality `c=1/12` would make the
joint coefficient `1/8`. These are sufficient targets before restoration and local
input accounting, not claimed graph theorems or circuit lower bounds.

Markov and Shi prove contraction complexity equals `tw(L(G))` in their tensor
model (Proposition 4.2) [markovshi08][markovshi08]. This supplies useful search
machinery and structural intuition. A bound on intermediate tensor rank alone does
not prove a bound on complete transition records: input tensors, symbol dimensions,
and the joint operation must use the same convention. Tree contraction also permits
nonlinear nesting rather than a single prefix chain.

## Symmetric submodular connectivity and signal hypergraphs

For a signal `s`, let `H_s` be its occurrence vertices. The hypergraph cut function
`f(P)=#{s : H_s meets P and its complement}` is symmetric and submodular: this
follows for each individual hyperedge indicator by checking its membership pattern,
then summing. In this repository `signalCut_eq_hypergraph_cut` needs the proved
connectivity of each signal's occurrence graph. Arbitrary edge labels do not suffice.

Oum and Seymour develop branch-decomposition algorithms for symmetric submodular
functions, including cut-rank and matroid connectivity [oumseymour06][oumseymour06].
A current development is Korhonen and Oum's 2026 preprint: their Theorem 1.1 finds
a width-`k` branch decomposition or certifies none exists, for an oracle connectivity
function, in `2^O(k) gamma n^6 log n + 2^O(k^2) gamma n` time
[korhonenoum26][korhonenoum26]. Here `gamma` is oracle evaluation time. This makes
the repository's signal cut a plausible experimental decomposition objective.

The algorithm does **not** imply width `k=O(beta1)` with an improved constant, and
its output is a tree rather than an order. At a three-way merge, a crossing hyperedge
can meet two or three parts, so the graph identity above becomes only
`J <= (f(A)+f(B)+f(C))/2`. Direct optimization of the union can be sharper.
General complete-transition capacity has not been shown to be a symmetric
submodular set function; the oracle theorem cannot be applied to it automatically.

For two certified nonnegative symmetric submodular objectives, their sum is still
such an objective and can enforce a common decomposition. Optimizing a sum may
overcharge shared information; taking a maximum or minimum does not automatically
preserve submodularity. This is a route to a usable upper certificate, not a proof
that a small certificate exists.

## Codes and matroids: distinguish state from branch complexity

Kashyap identifies matroid pathwidth with minimum trellis **state** complexity,
using `lambda(P)=r(P)+r(S)-r(E)` without the matroid convention's optional `+1`
[kashyap08][kashyap08]. For the split equations `Lx+Ry=0`, the feasible shared
syndromes form `im L intersect im R`, of dimension
`rank L + rank R - rank [L R]`. This is the algebra already reflected in
`LinearBoundary`; it requires all equations relevant to the split.

The related but stronger cost is a trellis **branch** or local-constraint dimension.
For a linear code `C` and one ordered coordinate `i`, let `C_P` and `C_S` denote
shortened subcodes supported strictly before and strictly after `i`. The minimal
local constraint has dimension `dim C-dim C_P-dim C_S`. Kashyap's minimal tree
realization simultaneously minimizes edge-state and node-constraint dimensions
for a **fixed coordinate tree**; equation (20) gives the node formula
[kashyap09][kashyap09]. It does not choose a good tree for an arbitrary circuit.

The checker enumerates actual binary quotient classes. The full length-three code
has maximum state dimension zero but branch dimension one; the even-parity code
has state dimension one but branch dimension two, in every coordinate order.
Thus charging one adjoining state can undercount a transition. Charging both states
separately can overcount their common information. The repository's joint-code
construction is aimed at precisely this distinction.

Forney's normal-realization framework represents local constraints and shared
variables explicitly [forney01][forney01]; his later treatment relates cycle and
cut-space realizations to cycle rank and primal/dual descriptions
[forney18][forney18]. This suggests choosing a representation that exposes real
dependencies. It does not justify treating arbitrary nonlinear gate relations as
linear codes or dropping visible nonlinear interface values from the joint record.

There is a useful barrier to an indiscriminate tree advantage: Kashyap and Thangaraj
prove that MDS and Reed–Muller codes have equal optimum tree and trellis **constraint**
complexity. For an `[n,k]` MDS code it is `min(k,n-k+1)`
[kashyapthangaraj12][kashyapthangaraj12]. Their word “trelliswidth” charges constraints;
Kashyap 2008's trellis-width charges states. These conventions must remain separate.

Jeong, Kim, and Oum give a constructive FPT algorithm for matroid pathwidth over
each fixed finite field, also treating subspace arrangements and linear rank-width
[jeong17][jeong17]. It can optimize small affine examples. It provides no universal
capacity supply bound in the linear-width regime relevant here.

## Rank-width, Boolean-width, and mim-width are semantic leads

Cut-rank is the rank over `F_2` of the **adjacency** submatrix across a vertex cut;
rank-width minimizes its maximum on decomposition trees [oumseymour06][oumseymour06].
Linear rank-width uses a vertex order [jeong17][jeong17]. Neither is automatically
the rank of a circuit's gate-equation system, its mixed Hessian, or its feasible
transition space. A correspondence with one of those objects must be proved.

Boolean-width charges the logarithm of the number of distinct unions of
neighbourhoods across a cut [buixuan11][buixuan11]. Mim-width charges the largest
induced matching in the bipartite graph of crossing edges; the linear version
restricts the decomposition to an order [bakkane22][bakkane22]. These encode different
equivalence relations, valuable when future computation depends only on the
associated neighbourhood information. An arbitrary basis does not guarantee that.

For example, the adjacency matrix across a nontrivial clique cut has rank one and
only two neighbourhood unions, while its edge count is `|P||S|`. This elementary
example explains possible semantic savings and why low graph cut-rank is not an
encoding of all independent wire values. It does not assert the clique is subcubic.
On the actual bounded-degree networks, a useful result must prove which assignments
become equivalent under **every continuation**, then control those classes globally.

## Knowledge compilation supplies antecedents, not a free constant

Amarilli, Capelli, Monet, and Senellart's Theorem 4.4 compiles a Boolean circuit of
pathwidth `k` into a complete unambiguous OBDD of width at most `2^(2(k+1))`
[amarilli20][amarilli20]. The visible factor two in the exponent matters for this
project: singly exponential dependence alone does not preserve the desired frontier
coefficient. The source's circuit basis and representation also need matching.
Its monotone CNF/DNF lower bounds are representation-specific, not universal supply.

Bova, Capelli, Mengel, and Slivovsky connect DNNF certificates to rectangle covers;
decomposability permits the certificate-splicing argument
[bova16][bova16]. This supports the method's demand side and its tree extension.
To improve a numerical circuit bound through compilation, one still needs a supply
theorem with explicit exponent, compatible semantics, and controlled representation
size. Ordinary branching-program state counts do not by themselves bound the number
of complete transitions used in the weighted frontier argument.

## Concrete next steps and the common-order obstruction

1. Search and optimize **subcubic pathwidth or linear-width** with the same numerical
   target as cutwidth; the conversions above lose only constants.
2. Test **vertex congestion / `tw(L(G))+1`** as the exact graph merge objective.
   Prove restoration into the existing tree demand theorem before reporting a coefficient.
3. For affine examples, optimize **joint constraint dimension plus visible nonlinear
   interface capacity**, rather than matroid state width alone.
4. Use the 2026 connectivity-function algorithm as a structural/experimental tool
   when an efficiently evaluable submodular certificate has actually been established.

Separate optimal orders are insufficient even for elementary cut functions. On four
vertices, the matchings `{12,34}` and `{13,24}` each have cutwidth one, but every
common vertex order has a cut where at least one has width two. The subset-DP checker
verifies this exact example. A proof promising small graph width and small code width
must therefore construct a common order or directly bound their joint objective.

## Known limitations

This is a targeted parameter review, not an exhaustive bibliography. Full texts were
inspected at the relevant theorem/definition sections, not independently re-proved in
their entirety. Golovach's original text and Forney 2001 were not fully accessible;
their roles and access depth are recorded below. No universal improvement or new Lean
theorem is claimed. The finite checks validate examples and conventions only.

[amarilli20]: ../sources.md#amarilli20
[bakkane22]: ../sources.md#bakkane22
[bova16]: ../sources.md#bova16
[buixuan11]: ../sources.md#buixuan11
[fomin03]: ../sources.md#fomin03
[forney01]: ../sources.md#forney01
[forney18]: ../sources.md#forney18
[golovach93]: ../sources.md#golovach93
[harveywood18]: ../sources.md#harveywood18
[jeong17]: ../sources.md#jeong17
[kashyap08]: ../sources.md#kashyap08
[kashyap09]: ../sources.md#kashyap09
[kashyapthangaraj12]: ../sources.md#kashyapthangaraj12
[kinnersley92]: ../sources.md#kinnersley92
[korhonenoum26]: ../sources.md#korhonenoum26
[markovshi08]: ../sources.md#markovshi08
[oumseymour06]: ../sources.md#oumseymour06
[seymourthomas94]: ../sources.md#seymourthomas94
