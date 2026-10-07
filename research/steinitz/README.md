# Incidence signing and the Steinitz method

The direct graph-incidence specialization of OpenAI's Euclidean Steinitz–Bergström
argument cannot improve the frontier layout coefficient. There is an exact
obstruction: signing incidence vectors never decreases the squared norm of a
prescribed prefix. This deduction is proved in
[Incidence.lean](../../Frontier/Layouts/Incidence.lean). It rules out this
particular transfer, not better graph layouts or stronger circuit lower bounds.

The current cubic layout target is `cutwidth <= (p+o(1))h`, where
`p = (3/(2*pi))*acos((1+2*sqrt(2))/4) = 0.1403509686358236`.
The corresponding cycle-rank coefficient is `A=2p` and the circuit coefficient
is `L=1+1/A=4.562497678925...`. These constants are unchanged by this investigation.
See [the existing layout theorem](../../Frontier/Layouts.lean).

## The mechanism in the source

[OpenAI's manuscript][paper] proves a common absolute `C` for two statements:
unit Euclidean vectors in any prescribed order admit signs bounding every
signed prefix by `C*sqrt(d)`; a zero-sum family admits a permutation bounding
every unsigned prefix by the same quantity. The actual Lean declarations are
[`SignedPrefixBound`, `OrderingPrefixBound`][model], and [`main`][main].

The analytical construction has three relevant features:

1. A contracted state receives one new scalar coordinate per step. A single
   convex body constrains all those states. Adaptive shifts exactly cancel the
   contractions, leaving an actual signed partial sum.
2. An additive matrix energy measures variation of the state maps. Spectral
   decomposition and Gaussian chaining control all prefixes without paying
   for their number. Gaussian correlation combines the constraints; an
   Ornstein–Uhlenbeck survival estimate gives a uniform Dirichlet-energy bound.
3. Chobanyan's transference lists positive vertices forward and negative
   vertices backward. If the original unsigned prefixes have norm at most
   `B` and the signed prefixes at most `D`, the new order has norm at most
   `(B+D)/2`. Applying this to a minimizing order yields the ordering theorem.

The first two steps are in [the construction][assembly], [matrix estimates][matrix],
and [survival argument][survival]. The third is stated and proved in
[the introduction][paper] and [`Transference.lean`][transference]. The source
credits [Chobanyan's 1994 transference principle][chobanyan] and the explicit
[2023 rearrangement argument][rearrangement]; this ordering operation is not
new to OpenAI or to Frontier.

## The exact incidence obstruction

Orient every edge arbitrarily. Set
`b_v(e) = 1_{src(e)=v} - 1_{tgt(e)=v}`. The total sum is zero.
For a vertex region `S` and signs `epsilon_v` in `{-1,1}`, let `c(S,epsilon)`
count edges inside `S` whose endpoints have opposite signs. Then

```text
|| sum_{v in S} epsilon_v b_v ||_2^2
    = |delta(S)| + 4*c(S,epsilon).
```

A boundary edge has exactly one selected endpoint, so its squared coordinate
is one regardless of the sign. An internal edge has squared coordinate zero
when its endpoint signs agree and four when they disagree. All other edges
contribute zero. Parallel edges are counted separately; loops contribute zero.

Thus, for every fixed ordering `pi`,

```text
min_epsilon max_k || sum_{j<=k} epsilon_{pi(j)} b_{pi(j)} ||_2^2
    = max_k |delta(S_k)|
    = width(pi).
```

The lower bound holds separately at every prefix. Giving every vertex the
same sign attains equality at every prefix simultaneously. The Lean theorem
`exists_signed_incidence_bound_iff` proves the stronger statement for an
arbitrary indexed family of regions and arbitrary region-specific budgets.
`sum_incidenceVector` checks the identification with actual vertex-incidence
sums, and `incidenceEnergy_signedIndicator` proves the exact energy identity.

Consequently, the norm estimate `(B+D)/2` cannot certify a strict improvement:
every signing has `D>=B` when `B` is the actual maximum prefix norm. Even if
one first selects a favorable order, establishing the desired signed-energy
bound already establishes the desired unsigned cut bound in that order.
Improving the analytical constants alone cannot remove this obstruction.

For a connected loopless cubic graph on `h` vertices, `||b_v||=sqrt(3)` and the
incidence span has dimension `h-1`. Normalization would turn an ordering bound
`C*sqrt(d)` into `cutwidth <= 3*C^2*(h-1)`. Beating `p*h` would require
`C<sqrt(p/3)=0.216295...`. But in a cubic bipartite graph, listing one
bipartition first creates a prefix with all `3h/2` edges crossing. Every
signing has energy at least `3h/2` there. A uniform prescribed-order incidence
signing constant must therefore satisfy
`C >= sqrt(h/(2*(h-1)))`, approaching `1/sqrt(2)=0.707106...`.

## What reordering can still change

The signed-energy obstruction does not say that the actual reordered layout
cannot improve. It says the source's norm bound cannot certify that improvement.
The exact quantity for its ordering operation is more informative.

At an original prefix `S`, partition its vertices into positive `P` and
negative `M`. Write `a=e(P,V\S)`, `b=e(M,V\S)`, and `c=e(P,M)`. Then

```text
|delta(S)| = a+b
|delta(P)| = a+c
|delta(M)| = b+c
max(|delta(P)|,|delta(M)|) = c + (a+b+|a-b|)/2.
```

In the positive-forward, negative-reverse order, the prefixes are exactly the
positive parts of original prefixes and the complements of their negative
parts, allowing repetitions and omitting duplicates. Complementary cuts have
the same size. Its cutwidth is therefore

```text
max_k [ c_k + (|delta(S_k)| + |a_k-b_k|)/2 ].
```

This is a tradeoff between separating internal edges and balancing the two
parts' boundaries to the outside. A useful adaptation must control both
quantities with one global sign assignment. A bound on the signed Euclidean
norm alone discards the information needed here.

The exact split identity is Lean-checked as `cutSize_split`. Its corollary
`cutSize_le_two_mul_max_split` proves that one of the two parts retains at
least half the original boundary. The ordering interpretation above is a
paper deduction, also checked exhaustively on small instances.

In particular, **one such reordering can never reduce cutwidth by more than a
factor of two**. For the cubic cyclic ladder `C_m square K_2` with even `m>=4`,
the bipartition-first order has width `3h/2`, so every single reordering of
this form has width at least `3h/4`. Yet listing the two vertices of each rung
consecutively around the cycle has width at most five. This holds for
arbitrarily large even `m`; the obstruction is not caused by intrinsically
large graph cutwidth. Exhaustive sign enumeration gives:

| Vertices | Starting width | Best width after one reordering | Rung order width |
| --- | --- | --- | --- |
| 8 | 12 | 6 | 5 |
| 12 | 18 | 9 | 5 |
| 16 | 24 | 12 | 5 |

This example does not refute Chobanyan transference, which starts from a
minimizing order, nor does it rule out several reorderings or a different
algorithm. It shows why a direct implementation on an arbitrary order is
not a substitute for a new structural theorem.

## Implication for the next research step

The promising feature of the source is its control of an entire path through
one global energy budget. The incidence specialization shows that its
signed-walk objective is unsuitable for improving our coefficient.
Controlling more prefixes with the existing Gaussian leading term would
also leave `p` unchanged: our current theorem already controls all prefixes
up to lower-order error.

A concrete surviving target is to start with the existing Gaussian layout
construction and prove that one global split satisfies
`c_k + (|delta(S_k)|+|a_k-b_k|)/2 <= (p-eta)*h+o(h)` for every prefix,
with a fixed `eta>0` and an order and split chosen jointly. Neither the
Steinitz theorem nor the identities here supply this estimate. It requires
a new graph-structural argument. Another possibility is to change the
boundary representation so that genuine cancellation becomes available,
while preserving the circuit-to-layout counting theorem.

## Verification and provenance

The source links are pinned to OpenAI math commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, retrieved on 2026-10-06.
The upstream statements, proof construction, and transference source were
inspected; the upstream Lean development was not rebuilt or axiom-audited.
The graph obstruction is an independent deduction, with no priority claim.

[The standard-library Python check](check_incidence.py) independently compares
explicit incidence-vector sums with edge counts on all 1,100 simple graphs
through five vertices and all ternary coefficient choices: 254,254 cases.
It compares actual reordered layouts with the exact split formula in 24,979
graph/order/sign cases through four vertices. A further 27 energy cases and
48 ordering cases cover loops, parallel edges, and reversed orientations.
The ladder table is obtained by enumerating every sign assignment.
[The recorded output](expected.json) includes these counts and constants.

The local Lean proofs use only `propext`, `Classical.choice`, and `Quot.sound`,
as checked by [the axiom guards](Audit.lean). Reproduce with:

```sh
lake build --wfail
lake env lean research/steinitz/Audit.lean
python3 research/steinitz/check_incidence.py
```

[paper]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026/build/introduction.tex
[assembly]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026/build/assembly.tex
[matrix]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026/build/matrix.tex
[survival]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Euclidean-Steinitz-Bergstrom-theorem-September-24-2026/build/survival.tex
[model]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Steinitz/Model.lean
[main]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Steinitz/Main.lean
[transference]: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Steinitz/Transference.lean
[chobanyan]: https://doi.org/10.1007/978-1-4612-0253-0_1
[rearrangement]: https://www.viam.science.tsu.ge/others/ticmi/blt/vol27_1/3.pdf
