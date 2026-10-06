# Graph structure, codes, and computational reuse

[Corpus](../index.md) · [Exact join parameter](joins.md) ·
[Proof-complexity interfaces](proof-complexity.md)

This family primarily changes the **supply** side. A structural lower bound on a
particular wiring graph is not a lower bound on a function: the function may have
a different implementation. Any useful transfer must quantify over every circuit
implementing the hard target, or construct a cheap representation of every small
candidate circuit.

## Technique comparison

| Technique | Established resource/model | Frontier contact and precise obstacle |
|---|---|---|
| Separators, pathwidth, cutwidth | Size of graph boundaries under a linear layout | Already the main supply theorem. Better bisections help only after a recursion or layout argument controls every transition with its actual constants. |
| Branch decompositions and line-graph treewidth | Tree congestion/maximum joint boundary | The exact join parameter is `tw(L(G))+1`, including leaf costs; see [the derivation](joins.md). The missing theorem is a universal coefficient below `A` in terms of cycle rank, not an unspecified treewidth bound. [harveywood18][harveywood18] |
| Brambles, tangles, graph searching | Dual obstructions to small-width decompositions | Useful for certifying failure of a proposed supply theorem and finding extremal graphs. A large bramble proves that a particular graph cannot be compressed geometrically; it does not construct a better universal layout. [seymourthomas93][seymourthomas93] |
| Expansion, superconcentrators, disjoint paths | Connectivity and terminal routing | Excellent for multi-output demand. They can coexist with linear-size graphs, so maximal recovery alone does not imply superlinear gate complexity. [pippenger77][pippenger77] |
| Signal hypergraphs and submodular cuts | Number of distinct signals crossing a vertex partition | Already checked in the paper. Jointly choosing equality routing and layout can beat a fixed routing; the challenge is proving a saving for all circuit incidence patterns. |
| Matroid connectivity and code trellises | Dimension of feasible syndrome states | Already used by the affine interface. It is exact for a fixed linear split. Optimizing syndrome width separately from the nonlinear suffix is invalid. |
| Tree realizations of codes | Maximum local constraint dimension, rather than merely state dimension | A stronger vocabulary for the branching affine compiler: charge a whole local merge relation. Some codes benefit from trees, but MDS and binary Reed–Muller codes have equal optimal tree and trellis local constraint widths. [kashyap09][kashyap09] [kashyapthangaraj11][kashyapthangaraj11] |
| Code realization bounds on arbitrary graphs | Trade-off between local linear constraint complexity and graph width | Suggest a demand that combines graph and code structure rather than treating them as two independent bills. Their linear local constraints do not directly model an arbitrary nonlinear suffix. [kashyap08][kashyap08] |
| Tensor-network contraction | Number of simultaneously open indices in a contraction schedule | Supplies algorithms and explains the join union. General signed/complex contractions preserve a scalar sum, whereas our exact-demand argument needs sound positive support generation. [markovshi08][markovshi08] |
| Factor-graph duality and holographic changes of basis | Partition functions invariant under local transformations | Worth testing for counting independently. Cancellation can hide invalid local combinations, so preservation of the partition function alone does not preserve rectangle splicing. [forneyvontobel11][forneyvontobel11] |
| Pebbling and cumulative space | Memory and recomputation on a specified DAG | Introduces a principled way to retain circuit direction and charge production/recomputation. Ordinary circuit size charges a gate once even if its value persists across many cuts. A semantic simulation theorem is needed before a pebbling lower bound transfers. [alwenetal17][alwenetal17] |
| Crossing-sequence and time-space arguments | Communication across machine-tape boundaries or successive computational slices | The local splice resembles ours. Summing many cuts requires a common hard input/distribution and a charging bound on how often one computation is counted; a different hard input at each cut is insufficient. |
| Topological component counts | Height of algebraic computation/decision trees over the reals | A small computation can describe only a bounded number of connected components in the relevant lifted semialgebraic set. This controls a different domain and computational resource; a discrete Boolean cube and arbitrary truth-table gates do not inherit the theorem. [benor83][benor83] |

## A new structural conclusion from the existing branching demand

For the Boolean networks compiled from near-linear circuits, recognizing a dense
rectangle-free set, the existing tree-demand lemma and the standard line-graph
congestion identity imply

```
tw(L(G)) >= n-o(n).
```

This is a paper deduction combining an existing frontier theorem with a cited
graph theorem, not a newly verified Lean declaration. It strengthens the
structural obstruction from linear layouts to tree decompositions. It does not
change the numerical circuit coefficient without a stronger universal **upper**
bound for this parameter. Full assumptions and a finite checker are in
[joins.md](joins.md). In particular, each input has a unique read site and each
vertex reads at most one input; bounded graph degree alone is insufficient.

## Why nonlinear support is not automatically a matroid

The signal-count function in the current paper is symmetric submodular. Linear
rank is submodular too. It is tempting to replace these by the logarithm of the
number of feasible joint values and import the same decomposition theory.

Here is a concrete obstruction. On independent bits `a,b,c`, let

```
X = a AND b,   Y = b,   Z = b AND c.
```

Their joint support is `{(0,0,0)} union {(x,1,z):x,z in {0,1}}`, so

```
|supp(X,Y)| = |supp(Y,Z)| = 3,
|supp(Y)| = 2,              |supp(X,Y,Z)| = 5.
```

Consequently the support logarithm `H_0` violates submodularity:

```
H_0(X,Y)+H_0(Y,Z) = log2(9) < log2(10)
                 = H_0(Y)+H_0(X,Y,Z).
```

This is realized by two ordinary binary gates. It is a precise reason why the
existing submodular signal-cut theorem cannot simply be relabeled as a theorem
about nonlinear semantic capacity. It does not rule out a different symmetric
submodular upper envelope, nor a decomposition method not requiring submodularity.
The support counts are independently enumerated by the corpus checker.

## Three concrete research targets

1. **Joint constraint dimensions on trees.** For an affine-prefix/nonlinear-suffix
   circuit, construct an exact additive tree generator whose merge code is the
   dimension of the *joint* feasible relation on both child states, parent state,
   and locally exposed values. Prove reconstruction and an analogue of the
   additive threshold demand for that tree representation before using it.
   Existing additive path demand alone does not certify this extension.
2. **Simultaneous semantic decomposition.** Optimize a common decomposition of
   suffix incidence and affine-code constraints. The first experiment should
   compare the maximum joint dimension to separate maxima on the same order,
   then to optima attained on incompatible orders. Stop a proposed argument if
   it silently exchanges these minima and maxima.
3. **Geometric extremal search.** Search directly for graphs with large
   `tw(L(G))/beta1(G)` rather than optimizing individual tree boundaries. A
   family contradicting the quarter target would retire the purely geometric
   route to five while leaving semantic and restriction routes available.
   Small-graph ratios with constant-size overhead are not asymptotic evidence.

## What this cannot establish by itself

For the MDS and binary Reed–Muller families, the cited equality is a useful
stopping condition: changing a trellis into a tree cannot by itself reduce the
optimal local constraint width of the code. A common decomposition with an
additional nonlinear suffix is a different problem. State dimensions, local
constraint dimensions, and edge-boundary counts must remain separate parameters.

A totally regular matrix need not require superlinear arithmetic size. Give
independent edge weights to a bounded-degree linear-size superconcentrator. Each
minor of its transfer matrix is a polynomial that is nonzero: a suitable set of
vertex-disjoint paths allows a specialization making that minor a permutation
matrix. Their finite product is nonzero, so over an infinite field some choice
of weights makes every minor nonzero. Weighted sums of constant fan-in retain
linear size. The graph existence is classical [pippenger77][pippenger77]; the
specialization argument is the elementary deduction used here.

Thus a superlinear lower bound for a specified Cauchy map would need coefficient
structure or generation constraints beyond its pattern of nonzero minors. The
same lesson applies to Boolean circuits: semantic production and reuse must enter
any attempt to sum demands over many cuts.

[alwenetal17]: ../sources.md#alwenetal17
[benor83]: ../sources.md#benor83
[forneyvontobel11]: ../sources.md#forneyvontobel11
[harveywood18]: ../sources.md#harveywood18
[kashyap08]: ../sources.md#kashyap08
[kashyap09]: ../sources.md#kashyap09
[kashyapthangaraj11]: ../sources.md#kashyapthangaraj11
[markovshi08]: ../sources.md#markovshi08
[pippenger77]: ../sources.md#pippenger77
[seymourthomas93]: ../sources.md#seymourthomas93
