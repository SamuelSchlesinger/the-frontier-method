# The branching budget is line-graph treewidth

[Structural comparison](index.md) · [Corpus](../index.md)

**Status:** identification with an established graph parameter, and a deduction
from the paper's existing branching demand. No new numerical layout theorem and
no new Lean proof are asserted here.

Let `G` be a finite simple graph. Put its vertices at the leaves of a rooted binary
tree. At an internal node its two child regions are `W1,W2`, and the third region
is the complement of their union. The merge budget is

```
j(W1,W2) = |delta(W1) union delta(W2)|.
```

Include leaf cost `deg(v)` and let `B(T)` be the largest leaf or merge cost. Then

```
min_T B(T) = tw(L(G)) + 1.                                    (1)
```

Here `L(G)` has one vertex per original edge, and two are adjacent when their
original edges share an endpoint. For edgeless graphs use `tw(empty)=-1`.

To identify the budget, route each original edge along the unique path between
its endpoint leaves. At an internal tree node it contributes exactly when its
endpoints lie in different one of the three regions, which is exactly membership
in `delta(W1) union delta(W2)`. At a leaf it contributes once per incident edge.
Thus `B(T)` is vertex congestion. Harvey–Wood's Theorem 2.4 identifies the minimum
with line-graph treewidth plus one. Their Theorem 2.6 likewise identifies the
minimum **adjacent-frontier union** cost on a line with `pw(L(G))+1`.
[harveywood18][harveywood18]

Rooting an unrooted subcubic leaf tree by subdividing an edge creates one new
degree-two merge; its congestion is bounded by its neighboring node congestion.
Suppressing the root reverses this, so the rooted convention does not change (1).

## Consequence for the frontier method

Consider a Boolean network with bounded graph degree, a unique read site for
each read input, and at most a constant number of inputs read at each vertex.
Assume `log2(n+|V|)=o(n)`, as holds for polynomial-size networks. These conditions
hold for the binary circuit compiler, which reads at most one input per vertex.
Leaf processing then adds at most a constant number of input symbols to the code.
There is a smooth decomposable support representation of size at most

```
poly(n+|V|) * 2^(B(T)+O(1)).
```

Here is the support construction, without a trace-uniqueness assumption. For each
region `W` and assignment `sigma` to `delta(W)`, create a node representing its
input assignments admitting an internal completion with boundary `sigma`. At a
join, enumerate assignments to `J=delta(W1) union delta(W2)`. Each such assignment
selects the two child boundary states and their parent boundary state. Connect
the product of the child nodes to the union node for that parent state. The
product scopes are disjoint because inputs have unique read sites. Local
compatibility allows completions to glue, and every completion induces one of
these choices. Across **all** parent states a join creates `O(2^|J|)` nodes and
edges, not a further factor for each parent. Leaf truth tables cost
`2^(deg(v)+O(1))`. This proves the displayed bound.

This is a paper support argument. The repository's
[checked weighted tree bound](../../../Frontier/Tree/Network.lean) requires
a unique satisfying edge trace for each accepted input; the circuit compiler
provides that hypothesis. Exact counting likewise needs trace uniqueness (or
another multiplicity argument), whereas the support construction above permits
overlapping union alternatives.

Dense rectangle-free acceptance with `log K=o(n)` forces this representation to
have size `2^(n-o(n))`, by the already established decomposable threshold bound.
For a near-linear circuit, unused inputs are `o(n)`; fixing them yields the same
leading demand on the network's read inputs. Hence every tree satisfies
`B(T)>=n-o(n)`, and (1) gives

```
tw(L(G)) >= n-o(n).                                          (2)
```

The local read bound is essential. A single isolated vertex allowed to read all
inputs could apply the entire target predicate locally, with no graph boundary.
Bounded graph degree alone would not imply (2).

The cited identity is stated for simple graphs. The same path/bag argument extends
to loopless multigraphs with parallel edges represented as separate line-graph
vertices: all edges incident at one vertex still form a clique, and each routed
edge is counted separately. Alternatively, restrict the graph-theoretic target
to the simple cubic cores used by the existing compression theorem.

To improve the unrestricted coefficient, a sufficient new graph theorem for the
connected subcubic loopless networks supplied by the binary compiler is

```
tw(L(G))+1 <= B*beta1(G)+o(|V|),       B < A.                  (3)
```

The existing compiler would then give `s >= (1+1/B)n-o(n)`;
`B=1/4` would yield five. Equation (3) is **unproved**. Knowing only
`tw(G)` or maximum individual boundary does not supply (3) at the same constant.
Constructivity and efficient local operations would additionally be required
for the corresponding counting algorithm.

## Reproducible finite check

Run `python3 research/lower-bound-vantages/data/check_layout_identity.py`.
One subset recurrence optimizes binary region joins. An independent elimination
recurrence computes treewidth of the line graph by reconstructing filled edges
from eliminated components. The checker also independently optimizes adjacent
frontier unions and ordinary cutwidth.

The comparison covers all 1,099 simple labeled graphs on one through five
vertices, plus named examples. These tests verify the implementation against
the identity; they provide no evidence for the asymptotic coefficient in (3).
The ten-vertex tree with three two-leaf branches has join budget three and
optimal linear transition budget four, showing a real finite distinction.
The cubic examples tested here do not exhibit a strict join saving.

[harveywood18]: ../sources.md#harveywood18
