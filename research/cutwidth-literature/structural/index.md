# Structural reductions, separators, and the cost of restoring a layout

[Review home](../index.md) · [Short-cycle deductions](reductions.md) ·
[Search record](data/search-log.md)

The useful structural question is not merely whether a graph has a small separator.
It is whether a decomposition pays for all inherited boundary edges in the **same
ordering**, with a constant better than the Gaussian bound. The strongest immediately
applicable results concern additional graph structure. They do not cover arbitrary
compiled circuits.

## Source-to-application map

| Source and inspected statement | What it supplies | Consequence for this project |
| --- | --- | --- |
| Lipton–Tarjan, planar separator theorem [lt79][lt79] | A balanced vertex separator of size at most `2 sqrt(2n)` | Recursive ordering gives `O(sqrt(n))` cutwidth in bounded degree, for planar graphs |
| Alon–Seymour–Thomas, excluded-minor separator [ast90][ast90] | `O_H(sqrt(n))` separators for a fixed excluded minor | The same restricted-class improvement, with constants depending on the excluded minor |
| Huang–Hume–Kelly–Lam, Corollary 3.3 and Corollary 1.11 [hhkl26][hhkl26] | Explicit separator-profile sum; sharp growth rates for many bounded-degree families | Direct all-prefix supply bounds when a hereditary separator profile is known; coarse equivalence does not preserve our leading constant |
| Solé Pi, Theorem 1.2 [solepi25][solepi25] | `cw(G) = O(sqrt(pcr(G) + sum_v deg(v)^2))` for simple graphs | In bounded degree, `pcr(G)=o(n^2)` implies `cw(G)=o(n)`; no unrestricted crossing-number hypothesis is available |
| Dvořák–Norin [dn19][dn19] | Every subgraph having a balanced separator of order at most `a` implies `tw(G) <= 15a` | Structural certification, not a constant-preserving pathwidth/cutwidth conversion |
| Houdrouge–Miraftab–Morin, Theorem 1 [hmm25][hmm25] | Constructive alternative with constant `7915/139 < 56.943` | Useful proof architecture for managing a pre-existing boundary; numerically weaker than 15 |
| Bonnet–Korhonen–Le–Li–Masařík [bkllm26][bkllm26] | Linear-time construction of `O_H(sqrt(n))` separators in minor-free graphs | Improves algorithms on a restricted class, not the cubic extremal coefficient |
| Le, Theorem 2 [le26][le26] | `O(h sqrt(log h) sqrt(n))` separator for `K_h`-minor-free graphs | Interesting degree-independent structural technology; constants and excluded-minor dependence do not produce the desired cubic constant |
| Bodlaender et al., Lemma 16 [bodlaender25][bodlaender25] | Replacing cubic vertices by triangles changes cutwidth by at most an additive 2 | Gives an especially useful short-cycle reduction; a direct case check below refines the upper additive term to 1 |

## Which separator information is sufficient?

For a graph of maximum degree `d`, let `s(m)` bound a half-balanced vertex separator
in **every subgraph** on at most `m` vertices. A recursive ordering yields

```
cw(G) <= d * sum_{j=0}^{floor(log2 n)} s(n / 2^j).
```

This is the finite content of Huang–Hume–Kelly–Lam's Corollary 3.3. Their 2026 corrected
arXiv version is used; its Proposition 1.22 corrects a direction/factor error in the
published coarse-wiring statement. [hhkl26][hhkl26]

For `s(m) <= c m^a`, `a>0`, the geometric sum costs at most
`d c n^a/(1-2^(-a))`. For constant separators the sum is logarithmic. These calculations
explain why treewidth-one trees can have logarithmic cutwidth, and why sublinear
power-law separators yield a genuinely sublinear layout.

**Deduction.** If a bounded-degree hereditary class has `s(m)=o(m)`, then the sum is
`o(n)`: fix a cutoff `M` beyond which `s(m)<=epsilon*m`; the large terms total at most
`2 epsilon*n`, while the finitely many smaller scales contribute a constant depending
on `M`. A single small separator in the whole graph does not meet this hypothesis.

For linear separators, the constants matter: the crude sum becomes `2dc n`. At degree
three it would need `c < p/6 ≈ 0.0233918` to beat the present coefficient. This is a
sufficient condition for this particular accounting, not a necessary condition for
better layouts. The profile theorem is excellent for restricted classes and an
unpromising black-box replacement for the cubic Gaussian argument.

## Why recursive bisection alone loses

Suppose an induced subgraph on `m` vertices admits a balanced **edge** cut of size
`b m`, uniformly throughout a recursion. Concatenating the two child orders gives
the valid but crude recurrence `W(m) <= b m + W(m/2)`, hence `W(n)<=2bn+O(1)`.
The boundary from ancestors stays active. Improving a single bisection from `n/6`
to, say, `0.139822n` therefore cannot be inserted into this recurrence to beat `p n`.

The classical Fomin–Høie route uses a stronger anchored completion lemma; its own
`1/6` bottleneck is analyzed in [the classical review](../classical/index.md).
An effective replacement should state a boundary-aware completion bound

```
completion width <= Phi(number of unprocessed vertices,
                        incoming ports, outgoing ports, internal cycle rank).
```

The parent and child estimates must decrease one common potential. Minimizing a
separate cut for each cardinality supplies no nesting or completion guarantee.

The boundary-balancing constructions in Houdrouge–Miraftab–Morin are conceptually
relevant here: ordinary balance does not automatically balance an already exposed
terminal set. Their theorem does not supply the small numerical constants needed
here. [hmm25][hmm25]

## Short cycles: usable savings and the remaining gap

The [worked reduction](reductions.md) proves the following elementary consequence
of triangle expansion, while crediting the published precedent [bodlaender25][bodlaender25].
If a connected simple cubic graph on `n` vertices contains `t` vertex-disjoint triangles,
contract all of them. The quotient is a loopless cubic multigraph on `n-2t` vertices.
Every quotient layout lifts with width at most **one greater**. Consequently, using
the repository's proved logarithmic restoration theorem,

```
cw(G) <= (p + epsilon)(n-2t) + O_epsilon(log n).
```

This is a proved-on-paper restricted-class deduction, supported by exhaustive local
checks; it is not a new Lean declaration or a novelty claim. A packing covering about
`1.563%` of the vertices already supplies the reduction to `5/36` on that class.
A packing covering about `16.407%` supplies `1/8`. Rounding and strict slack should
be retained in applications. Triangle-free graphs remain completely untreated by
this saving.

Contracting a longer cubic cycle produces a vertex with more than three ports.
Replacing it by a tree can change the interleaving required by the outside layout.
One cannot assume the triangle lifting proof extends with the same constant.
A useful research program is to classify bounded port gadgets and prove **layout
replacement inequalities with an explicit gain in the same cycle-rank budget**.

The deletion calculation in [reductions.md](reductions.md) quantifies another trap:
even if a high-girth coefficient were available for a residual subcubic graph,
paying `3|U|` to restore deleted vertices rapidly destroys a gain of order `0.001n`.
The hard case is neither automatically high-girth nor automatically cheap to repair.

## Higher degrees and weighted potentials

The current code already compresses a maximum-degree-`d` multigraph into a core with
degrees between 3 and `d`, and charges its edge count to cycle rank. Local degree and
correlation information is then replaced by a worst-case degree bound. A prospective
improvement should retain those data together and optimize a weighted incidence
potential, rather than optimizing the density estimate and the correlation estimate
independently.

Edwards–McDermid is a serious precedent, but its admissible parameter interval and
increment inequalities exclude direct substitution of `p`; see
[classical/index.md](../classical/index.md). The relevant new theorem would be an
explicit feasible system of reduction inequalities for a richer potential at
`p<1/6`, plus a cutwidth restoration proof.

## Circuit-specific structure

Planarity, minor exclusion, a small pair-crossing number, or a uniformly sublinear
separator profile would give strong specialized results. None follows merely from
acyclicity of the original circuit: every undirected graph has an acyclic orientation
obtained from a vertex order. This observation does not prove that every cubic graph
occurs as a compiled circuit, but it rules out using acyclicity alone as the missing
structural theorem.

Small-cut decompositions are still worth combining with Gaussian layouts on difficult
pieces. The combined proof must record boundary cost at each piece and bound either
the maximum active boundary along a path or the union of all boundaries at a tree
merge. See [related parameters](../parameters/index.md).

## Prior high-girth investigation

An older project research summary reports a high-girth candidate/certificate near
`0.138781` and a numerical 123-type covariance-cone target. The original temporary
certificate scripts were not present at their recorded paths during this review.
Accordingly neither number is used here as a newly verified theorem, external
literature result, or established all-graph improvement. Recovering a durable proof
and certificate is a prerequisite to building on that particular calculation.

[ast90]: ../sources.md#ast90
[bkllm26]: ../sources.md#bkllm26
[bodlaender25]: ../sources.md#bodlaender25
[dn19]: ../sources.md#dn19
[hhkl26]: ../sources.md#hhkl26
[hmm25]: ../sources.md#hmm25
[le26]: ../sources.md#le26
[lt79]: ../sources.md#lt79
[solepi25]: ../sources.md#solepi25
