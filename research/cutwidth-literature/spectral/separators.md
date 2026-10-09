# Spectral separators and global layout relaxations

[Spectral review](index.md) · [Structural accounting](../structural/index.md) ·
[Layout algorithms](../classical/algorithms.md) · [Application](../synthesis.md)

These methods can find cheap divisions before completing layouts of the pieces.
They supply no verified universal cubic coefficient below `p = 0.1403509686...`.
The missing object is a layout with prescribed exterior ports, or rounding that
bounds every prefix of one order.

## Spectral gaps: lower certificates and selected sweep cuts

Use `L_comb=D-A` for the combinatorial Laplacian and
`L_norm=I-D^(-1/2) A D^(-1/2)` for the normalized one, on graphs without isolated
vertices. Write their second eigenvalues as `lambda2` and `mu2`, respectively.
For a `d`-regular graph, `lambda2=d*mu2`.

Alon–Milman Lemma 2.1 and Remark 2.2 give the spectral bisection lower bound:
`cw(G) >= lambda2*n/4` for even `n`, or `3*mu2*n/4` for cubic graphs.
Their first positive combinatorial eigenvalue is named `lambda1`.
This obstruction follows directly from the centered-indicator Rayleigh quotient.
[alonmilman85][alonmilman85]

For `d`-regular graphs, conductance is
`phi(S)=|delta(S)|/[d*min(|S|,|V\S|)]`.
The usual spectral sweep sorts a second eigenvector and selects the threshold
with **minimum conductance**. Kwok–Lau–Lee–Oveis Gharan–Trevisan state
`mu2/2 <= phi(G) <= sqrt(2*mu2)` and sharpen the guarantee for this same sweep:
Theorem 1.2 of the inspected 2013 preprint gives
`min_t phi(S_t) <= O(k)*mu2/sqrt(mu_k)`.
Their Theorem 1.4 also finds a `1/5`-balanced separator with conductance
`O(k*epsilon/mu_k)`, where `epsilon` is the minimum-bisection conductance.
[kwoketal13][kwoketal13]

The sweep sets are nested, but their **maximum edge boundary** is uncontrolled.
Recursion also inherits earlier cuts. Induced pieces need not remain regular,
so volume balance and vertex-count balance differ. A universal proof needs an
alternative for pieces without useful spectral gaps and a common boundary budget.

## ARV: strong metric geometry, with an average-over-radii guarantee

Arora–Rao–Vazirani obtain an `O(sqrt(log n))` approximation for sparsest cut and
related partition problems. Their SDP uses squared Euclidean distances satisfying
triangle inequalities and a spreading constraint. Positive semidefiniteness alone
does not impose these metric and balance constraints. [arv09][arv09]

In the inspected manuscript dated 2004-04-12, Theorem 1 finds two linear-size sets
separated by `Omega(1/sqrt(log n))`; Corollary 2 gives a constant-balanced cut.
Here `W=sum_edges ||v_u-v_v||^2` is four times the SDP objective, and the expansion
bound is `O(W*sqrt(log n)/n)`. The journal publication is 2009.
[arv09][arv09]

Region growing bounds an integral of the ball boundary by total edge length,
giving a good radius rather than a bound for every radius. A cubic improvement
needs sharper recursive accounting or rounding; the growing approximation factor
cannot itself improve `p`.

## Reweighted spectra and prescribed vertex measures

Kwok–Lau–Tung's 2025 Theorem 1.4 connects weighted vertex expansion to a
reweighted spectral gap. For a positive probability measure `pi`, their definitions
are `psi=min{1, min_(0<pi(S)<=1/2) pi(partial S)/pi(S)}` and
`lambda2*=max_P lambda2(I-P)`, where `P` is a reversible stochastic matrix
supported on graph edges and holding probabilities, with stationary measure `pi`.
They prove `psi^2/log d <= O(lambda2*)` and `lambda2* <= O(psi)`, where `d>=2`
bounds the maximum degree. The logarithmic factor is independent of graph size
in bounded degree.
[kwoklautung25][kwoklautung25]

Weighting vertices with exterior ports may help choose a split. The theorem does
not guarantee cardinality balance, prescribed terminal sides, or all-prefix cost.
Its constants give no verified `0.14`-scale estimate, and reweighting does not
change the wire multiplicities charged by the final layout.

## An existing SDP specifically represents all pivot cuts

Bansal–Katzelnick–Schwartz Section 6.3 goes beyond the approximation result
summarized in the [algorithmic review](../classical/algorithms.md). Their `SDPCW`
assigns unit vectors `u_y^x` for each pivot `x` and vertex `y`, inducing metrics
`d_x(y,z)=||u_y^x-u_z^x||^2/4`. Triangle, orthogonality, and spreading constraints
link the construction; equation (36) requires

```
sum_{yz in E} d_x(y,z) <= C                 for every pivot x.
```

Every actual order gives a feasible assignment, so the optimum is a **lower bound**
on cutwidth. Lemmas 17–18 give spreading squared-Euclidean metrics on every subset.
Fractional feasibility does not produce nested integral cuts; Open Question 5
asks for better rounding, with ARV machinery proposed in the section.
[bansal24][bansal24]

A sufficient new route would prove, uniformly for cubic graphs,
`SDPCW(G) <= b*n+o(n)` and `cw(G) <= rho*SDPCW(G)+o(n)`, with `rho*b<p`.
Neither estimate at useful constants is supplied here. A low SDP value alone
cannot give a layout upper bound. This proposed rounding framework has a different
role from the Gaar–Puges–Wiegele finite optimization study.

## A concrete completion objective with exterior ports

The following bookkeeping is a deduction for this review. Let `H` be a piece
that will be placed consecutively in an order. At each vertex let `ell(v)` count
edges to exterior vertices already placed, and let `r(v)` count edges to exterior
vertices placed later. Cubic pieces obey `deg_H(v)+ell(v)+r(v)<=3`.
For an interior prefix `S`, its variable frontier contribution is exactly

```
F_H(S) = |delta_H(S)| + sum_(v outside S) ell(v) + sum_(v in S) r(v).
W(H;ell,r) = min_order max_prefix F_H(prefix).
```

Edges crossing entirely outside the piece contribute a separate fixed constant.
The endpoint cuts already force `W>=max{ell(V(H)),r(V(H))}`. A low-conductance
cut of `H` alone can miss both port terms.

Partition `V(H)=X disjoint-union Y`
and put `X` before `Y`; let `d_Y` and `d_X` count edges to the opposite part.
Write `ell(Y)=sum_(v in Y) ell(v)` and similarly for `r(X)`. Then

```
W(H;ell,r) <= max{
  ell(Y) + W(H[X]; ell|X, r|X+d_Y),
  r(X)   + W(H[Y]; ell|Y+d_X, r|Y)
}.
```

Inside `X`, the incoming ports of untouched `Y` remain active; inside `Y`, the
outgoing ports of completed `X` remain active. This counts every frontier edge
and proves the inequality by choosing optimal child orders. Parallel edges count
individually. No improved universal estimate or Lean theorem is claimed.

**Research target.** Find a potential `Phi(H;ell,r)` that bounds this completion
cost, is preserved by useful spectral/SDP splits through the displayed rule,
and satisfies `Phi(G;0,0)<=(p-delta)|V(G)|+o(|V(G)|)` for every cubic input,
for fixed `delta>0`. Gaussian layouts or patches can handle pieces where splitting
is too expensive. This states the missing [anchored completion](../classical/index.md)
theorem; weighted spectral objectives alone do not prove it.

## Search and access record

Checked 2026-10-09. Queries: exact Alon–Milman/ARV titles; `Improved Cheeger
inequality higher order spectral gap`; `Cheeger vertex expansion reweighted
eigenvalues`. Four new records follow; `bansal24` already exists. Relevant sections
were read, not independently re-proved in full. ARV's Berkeley download succeeded;
Princeton returned a non-PDF and ACM access failed. Publisher-deposited DOI metadata
verified the 2009/2013 records; the final 2025 PDF matches publisher metadata.
No SDP was solved or universal improvement certified. This focused addition does
not exhaust spectral partitioning, embeddings, flows, or expander decompositions.

[alonmilman85]: ../sources.md#alonmilman85
[arv09]: ../sources.md#arv09
[bansal24]: ../sources.md#bansal24
[kwoketal13]: ../sources.md#kwoketal13
[kwoklautung25]: ../sources.md#kwoklautung25
