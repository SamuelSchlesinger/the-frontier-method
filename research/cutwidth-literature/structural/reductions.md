# Two explicit short-cycle accounting checks

[Structural review](index.md) · [Executable checks](data/check_reductions.py)

These are elementary deductions made during the review. They are paper arguments,
not new formalized theorems. No historical novelty is claimed. The triangle
replacement precedent is Bodlaender et al., Lemma 16 [bodlaender25][bodlaender25].

## Simultaneous triangle expansion costs at most one

Let `Q` be a loopless cubic multigraph, and replace any subset of its vertices by
disjoint triangles, assigning one original incident edge to each triangle vertex.
Call the expanded graph `G`. Then

```
cw(G) <= cw(Q) + 1.
```

Take any layout of `Q`. At each expanded vertex, list the three triangle vertices
consecutively, placing ports to earlier quotient vertices first. Let `a` be the number
of earlier ports and `3-a` the later ports. Let `B` count edges crossing the position
that are not incident to this quotient vertex. The cuts immediately before and after
the block have sizes `B+a` and `B+3-a`.

After `j=1,2` triangle vertices, exactly two internal triangle edges cross. Since
earlier ports are processed first, the complete cut size is

```
B + 2 + max(a-j, 0) + max(j-a, 0) = B + 2 + |a-j|.
```

For `a=0,1,2,3` and `j=1,2`, this is at most
`B + max(a,3-a) + 1`. Between blocks the cut size is unchanged. Only one block is
partially processed at any instant, so the additive one does **not** accumulate
over expanded vertices. This proof counts parallel edges individually.

Bodlaender et al. give the same layout construction when every vertex is expanded,
using the sufficient upper bound `cw(Q)+2`. The direct four-case calculation above
refines that additive estimate; the leading-constant benefit comes from reducing
the vertex count, not from replacing 2 by 1. [bodlaender25][bodlaender25]

Conversely, contracting a vertex-disjoint triangle packing in a simple cubic graph
produces a loopless cubic multigraph: each triangle has exactly three external
incidences. Each contracted triangle removes two vertices and three edges, so for
a connected graph the cycle rank decreases by exactly one.

For `t` disjoint triangles in a connected cubic graph on `n` vertices, the quotient
has `n'=n-2t` and `beta(Q)=n'/2+1`. The checked repository theorem
`CubicLayoutBound.exists_layout_log` therefore gives, for every `epsilon>0`,

```
cw(G) <= (p+epsilon)(n-2t) + O_epsilon(log n).
```

The implicit constant absorbs the cycle-rank `+1` and the triangle-lifting `+1`.
Since `t<=n/3`, the quotient still has at least `n/3` vertices. Disconnected graphs
can be ordered component by component; the displayed application is stated for
connected graphs to avoid changing the cycle-rank convention.

If the packing covers a fraction `f=3t/n`, its leading coefficient is
`p(1-2f/3)`. The validation script reproduces the threshold fractions. This only
improves a restricted class: it supplies no saving for triangle-free graphs.

## Why deleting short cycles may be too expensive

For a graph of maximum degree `d` and a vertex set `U`, an ordering of `G-U` can be
extended by placing `U` first. At every cut at most `d|U|` additional edges need be
charged, giving the elementary bound

```
cw(G) <= cw(G-U) + d|U|.
```

If a coefficient `c` applies to the **remaining subcubic graph** on `n-|U|` vertices,
this proves only

```
cw(G) <= c n + (3-c)|U| + o(n).
```

Thus beating `p n` by this estimate requires
`|U|/n < (p-c)/(3-c)`. For the illustrative `c=0.138781`, the fraction is about
`0.000549` (roughly `0.055%`). This number is an arithmetic illustration, not an
endorsement of an independently verified high-girth theorem at that value.
An estimate for cubic graphs of large girth is also not automatically an estimate
for the nonregular residual graph.

Similarly, deleting `k` edges can be restored for at most `k` extra width along the
same order. Neither calculation rules out a better repair argument; it identifies
what the naive one actually pays.

[bodlaender25]: ../sources.md#bodlaender25
