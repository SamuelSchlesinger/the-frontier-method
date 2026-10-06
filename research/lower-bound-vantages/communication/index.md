# Communication, information, and coherent semantic states

The useful transfer is a smaller **sound representation of the whole accepting
set**, with a proved transition budget. Low communication cost at separate cuts
does not supply that representation. This page gives a representative-quotient
lemma that preserves unambiguity and two finite examples isolating the failures.
These are elementary deductions, not claims of historical novelty or new Lean theorems.

The target remains single-output unrestricted `B2`, arbitrary fan-out, and `s`
positive-arity gates on `n` used inputs. For dense rectangle-free fibers, the
existing demand is `D >= 2^(n-o(n))`. A compiler with
`log2 D <= B(s-n)+o(n)` would give coefficient `1+1/B`; improvement requires
`B < A = 0.2807019372716472...`, and five requires `B <= 1/4`.
The [root](../index.md) records the unused-input and restriction qualifications.

The [existing communication note](../../communication/README.md) already proves
capped masses, fractional moments, and conditional encoding potentials, crediting
Sam McGuire for weighted disjoint peeling. The [additive](../../communication/additive.md)
and [joint-code](../../communication/joint.md) notes already handle affine syndromes,
overlapping additive labels, and joint visible-signal rank. None is a new proposal here.

## Gate tests, KW relations, and circuit sharing

Fusion organizes a lower bound around locally inconsistent combinations of valid
computations; the admissible tests depend on the computational model. Wigderson's
framework does not identify arbitrary set covers with circuits at unit cost.
The distinction survives modern semifilter formulations. [wigderson93][wigderson93]
[pich22][pich22]

**Elementary gate-test lemma.** Let a witness be `(a,phi)`, where `phi` assigns bits
to Boolean functions, agrees with evaluation at `a` on inputs and constants, and
disagrees on `f`. A binary test `(h,u,v)` rejects a witness exactly when
`phi(h(u,v)) != h(phi(u),phi(v))`; include every binary truth table and the unary
tests. For any chosen witness family, a circuit for `f` supplies at most `s` tests
covering it: if all tests passed, induction through its DAG would give the correct
value at every gate, contradicting the output condition. This preserves `B2` costs.
It proves only `minimum test-cover size <= circuit size`. An arbitrary test list
need not be causally constructible, and restricting tests can invalidate this inequality.
The missing gain is a witness family with a stronger demand theorem, or a gate-aware
amortization recovering the `s-n` budget; changing the word “cover” supplies neither.

The KW relation instead gives Alice `x in f^-1(1)` and Bob `y in f^-1(0)` and asks
for a differing coordinate. Deterministic protocol trees characterize De Morgan
depth and formula structure; unfolding a shared circuit can duplicate gates.
The monotone version asks for `x_i=1,y_i=0`. [kw90][kw90]
Rectangle-DAGs impose a feasible rectangle at every node and a covering condition
at every branching step; they characterize monotone circuit size under the cited
size conventions. They are a substantive model of shared computation, not ordinary
protocol trees with identical labels casually merged. [ggks20][ggks20]
Transferring either result to unrestricted `B2` with a leading constant requires
accounting for nonmonotone truth tables and all conversion gates explicitly.

**Universal cover obstruction.** Every ordinary KW relation has a cover by at most
`2n` valid output rectangles: for each `i,b`, use
`{x:f(x)=1,x_i=b} x {y:f(y)=0,y_i=1-b}`, labeled `i`.
Every domain pair differs somewhere. Thus unstructured nondeterministic KW covers
cannot themselves encode an unrestricted superlinear gate lower bound. Evaluation
matrices below are different objects and do not inherit this `2n` upper bound.

## Which matrix measure controls which resource?

Fix a coordinate partition and the `0/1` evaluation matrix `M(x,y)=f(x,y)`.
For sign rank use `S=2M-1`. These ranks have different semantics.

| Measure | Exact resource connection | Missing frontier transfer |
|---|---|---|
| Ordinary real rank | A deterministic protocol with `c` bits partitions `M` into at most `2^c` monochromatic rectangles; hence `rank M <= 2^c`. An unambiguous acceptor also factors `M` through its cut states. | A small signed factorization is not a positive, sound splicing representation. |
| Boolean rank | Minimum number of all-one rectangles covering the support; equivalently Boolean-semiring factorization width and nondeterministic certificate cost up to encoding conventions. | Covers must admit common transitions between consecutive cuts. |
| Nonnegative rank | Minimum `r` in `M=UV`, `U,V>=0`; logarithm characterizes randomized communication computing matrix entries **in expectation**. [faenza15][faenza15] | Positive weights do not imply unique input generation, nor compatible factorizations across cuts. |
| Entrywise approximate real rank | For fixed error `epsilon`, minimize rank over matrices within `epsilon` of `M`; a private-coin `c`-bit protocol's acceptance matrix has rank at most `2^c`. | Approximate zeros allow false splices; bounded-error communication is not exact support generation. |
| Sign rank | Minimum real rank of a matrix with sign pattern `S`; logarithm characterizes private-coin unbounded-error communication up to additive constants. [paturi-simon86][paturi-simon86] | A sign-correct factorization permits cancellation and arbitrarily small margins, without a sound generator. |

The ordinary and approximate rank bounds follow directly by summing transcript
outer products; fixing a private-coin transcript separates its probability into
an Alice factor and a Bob factor. Public randomness is a different convention.
For a general nondeterministic acceptor, multiplying prefix/suffix path-count
matrices need not give `M`; Boolean multiplication gives its support instead.
Unambiguity is precisely what makes the path-count factorization equal `M`.
No ordering of all five measures, or rank-to-circuit equivalence, is assumed.

For the existing sumset route, a cut produces `A+B`, potentially with overlapping
coordinate support. Coordinate-rectangle rank is therefore not automatically the
right demand measure. The already proved additive threshold theorem is the valid
bridge; replacing its exact output set by a numerical factorization needs a new proof.

## Discrepancy, corruption, and information

Discrepancy controls signed mass of rectangles under a specified distribution;
corruption controls the error forced inside sufficiently large rectangles.
The partition bound adds global linear constraints on weighted rectangle families
and lower-bounds randomized communication, subsuming the corruption and generalized
discrepancy bounds in its communication setting. [jain-klauck10][jain-klauck10]
These are demand tools. The frontier target already demands nearly `n` bits from
any sound accepting representation; stronger demand cannot exceed the ambient
`2^n` input count in this particular charging argument. A coefficient improvement
must therefore improve supply, or change how the circuit is charged.

A concrete transfer to test is a **single** LP over all layers whose variables are
transitions and whose constraints enforce flow, sound continuation, and the same
input distribution. The logarithm of its optimum would need to be at least
`n-o(n)` on the hard target, certified by its dual, and at most `B(s-n)+o(n)`
for every `B2` circuit, with `B<A`.
Independent partition-bound optima omit those interlayer constraints. A fractional
cover also needs a positive realization theorem before existing pruning applies.

Internal information complexity concerns what the transcript reveals to the other
party; Braverman--Rao identify it with amortized communication for independent copies
of a communication task. Adjacent cuts of one circuit are dependent views of shared
signals, not independent copies. [braverman-rao14][braverman-rao14]
For an elementary warning, let every layer expose the same fair bit `Z`: each has
entropy one, while their joint entropy is one, regardless of the number of layers.
Summing marginal information charges the same computation repeatedly.

The existing conditional potential correctly amortizes one transition's encoding.
The missing theorem is a gate-derived bound on its **whole conditional path budget**,
uniformly over a coherent layout, or a restriction that removes the expensive case.
Shannon entropy, mutual information, and low-error interactive compression do not
replace the required capped masses or Renyi moments; the shared-selector example
in the existing note already rules out that shortcut. New semantic transitions
change their distributions, so their masses must be recomputed after recompilation.

## Exact compatibility between cuts

Write `L subset {0,1}^n` for the accepted language in one fixed input order.
At cut `t`, a layered acceptor gives the Boolean factorization
`1_L(pz) = OR_q U_t(p,q) V_t(q,z)` by prefix and suffix reachability.
To realize prescribed factors by one acceptor, there must be common edge relations
`E_t(q,a,r)` satisfying both recurrences:

```
U_(t+1)(pa,r) = OR_q U_t(p,q) E_t(q,a,r),
V_t(q,az)    = OR_r E_t(q,a,r) V_(t+1)(r,z).
```

With the start/accepting boundary factors, these conditions are also sufficient:
make `E_t` the edges and induct on prefixes and suffixes. This is a direct
compatibility certificate, stronger than separate small Boolean ranks.

**Counterexample to gluing prescribed optimal partitions.** Take
`L={000,100,101}`. After the first bit choose the disjoint rectangles
`{0,1} x {00}` and `{1} x {01}`. After the second choose
`{00} x {0}` and `{10} x {0,1}`. Both partitions use the minimum two rectangles:
each matrix has a zero obstructing a single rectangle containing all three ones.
The first cut's state with right language `{01}` would need, after reading `0`,
right language `{1}`. No union of the second cut's languages `{0}` and `{0,1}`
equals `{1}`. Hence no transitions realize these prescribed factors.
There **is** a width-two coherent acceptor using different factors. This refutes
automatic gluing, not the existence of equally small alternative representations.

There is a positive exception: for deterministic ordered reading, use the actual
residual languages `L_p={z:pz in L}`. Equality is a right congruence because
`L_p=L_q` implies `L_(pa)=L_(qa)`. The resulting partial deterministic acceptor
has exactly the number of distinct nonempty residuals at each layer, and no smaller
deterministic width is possible there. This is the semantic basis of canonical
ordered decision diagrams. [bryant86][bryant86]
It composes automatically, but residual count can greatly exceed Boolean rank.

## A quotient lemma that also preserves counting

**Representative-series lemma (proved here).** Consider a finite layered weighted
acceptor. At each layer, identify states with identical suffix series
`F_q(z)=sum_{paths q --z--> accept} product(edge weights)`.
Choose one representative of each class. Retain only its outgoing transitions,
redirect destinations to classes, and add weights of parallel transitions.
Keep the representative's terminal weight and aggregate initial weights by class.
Then the quotient has exactly the original weight for every complete word.

Proof: work backward from terminal weights. If the claim holds in the next layer,
the quotient's value at a class is the representative's sum over its outgoing
edges using unchanged successor series, hence equals `F_q` for every member.
Apply the same equality to the initial weighted sum. The proof also works over
the Boolean semiring, where addition is union and the series are right languages.

**Unambiguous corollary.** In a trim unweighted acceptor with at most one accepting
path per word, every state's suffix series is `0/1`: two suffix paths could be
prefixed by any path reaching that state, contradicting unambiguity.
Consequently equality of right languages implies equality of suffix series.
The representative quotient preserves unambiguity and exact word counts. With
unit weights and live states, a parallel multiplicity above one would itself force
an accepted word to have count above one, so no such multiplicity can occur.
This is a sound semantic compression rule beyond simply recording boundary values.

**The union quotient fails to count.** Let the first bit send `0` to `p`, `1` to
`q`. On the second bit `0`, let `p` go to `r`, and let `q` branch to `r0,r1`.
Let `r` accept either final bit, `r0` only `0`, and `r1` only `1`.
Originally each of `000,001,100,101` has one accepting path, and both `p,q` have
right language `{00,01}`. Merging them and retaining the union of outgoing edges
gives two accepting paths per word. Support stays correct; counting doubles.
Retaining `p`'s outgoing edges as representative restores the four original counts.

For a readily checkable sufficient condition on a proposed weighted partition,
let `C_t` be its state-to-class indicator matrix. The identities
`A_t(a) C_(t+1) = C_t barA_t(a)` and `beta=C_n barbeta` telescope to preserve
every word weight. These local identities are sufficient, not necessary for the
semantic representative construction; equal series can have different decompositions.

Two quantitative obligations remain. First, the lower bound charges **edges**:
width `W` in a simple length-`n` binary layered NFA gives only `D<=2nW^2`, whereas a
deterministic acceptor has `D<=2nW`. A claimed width exponent can lose a factor two.
Second, the lemma proves correctness once the equivalence is available; it supplies
no universal bound on the number of classes or retained transitions. An exact #SAT
algorithm further needs to construct the quotient within its advertised time bound.

## Knowledge compilation, lifting, and query adversaries

DNNF uses disjoint variable scopes at conjunctions; deterministic DNNF additionally
requires disjoint alternatives at disjunctions. Smooth deterministic representations
support direct model counting; arbitrary overlapping alternatives do not.
[darwiche-marquis02][darwiche-marquis02]
Multi-partition communication lower-bounds DNNF size through balanced certificate
rectangles. [bova16][bova16] The repository already proves stronger target-specific
threshold demand for smooth decomposable DAGs; it does not yet supply a cheaper
unrestricted `B2`-to-DNNF compiler. An approximate or weighted replacement also
needs a demand theorem compatible with overlapping certificates.

The checked Amarilli--Capelli--Monet--Senellart manuscript's Theorem 4.4 compiles
a circuit of pathwidth `k`, given its decomposition, to a complete uOBDD of width
at most `2^(2(k+1))`, in time `|P| O(2^((2+epsilon)k))`.
Its input basis is AND/OR/NOT. [amarilli20][amarilli20]
This is a useful semantic antecedent, but neither its basis conversion nor its
exponential constant can be suppressed when comparing with `A(s-n)`.
The missing transfer is a `B2` compilation/layout theorem with the actual retained
edge exponent below `A(s-n)`, including restoration, read-once input sites, and sharing.

Query-to-communication lifting turns hard query problems into hard communication
problems after gadget composition; randomized lifting and DAG lifting concern
different resources. [gpw17][gpw17] [ggks20][ggks20]
To improve this frontier coefficient, one needs either a gadget hard under every
layout-relevant partition at controlled original input length, or a direct
constant-preserving simulation from unrestricted `B2` to the lifted model.
A theorem for one designated Alice/Bob partition does not supply either property.

Span-program size counts labeled vectors; witness size is a separate quantity.
Karchmer--Wigderson's model and Reichardt's tight general-adversary characterization
of bounded-error quantum queries should therefore not be substituted for Boolean
gate size. [kw93][kw93] [reichardt11][reichardt11]
Query composition can reuse an input oracle at unit cost and has no unrestricted
circuit sharing charge. The missing bridge is an explicit simulation with a
measured size/witness parameter bounded by the `B2` excess `s-n`; none is supplied.

## Ranked directions and stopping conditions

1. **Representative semantic quotient.** Prove that every relevant `s`-gate circuit
   admits a sound coherent acceptor whose retained representative transitions obey
   `log2 D <= B(s-n)+o(n)` for some specified `B<A`. Five would require `B<=1/4`.
   Start by computing exact right languages on small compiled graphs and comparing
   retained edges with the existing joint-rank code. Stop an asserted local rule
   immediately if it changes support or path counts; the examples below are controls.
   The quotient lemma is proved; the uniform quantitative theorem is open.
2. **Conditional information versus simplification.** Prove that every residual
   circuit either has a compatible transition moment budget with coefficient
   `B<A`, or admits restrictions with enough gate saving to pay the existing
   restriction accounting. Test shared selectors, XOR sharing, and coded affine
   prefixes. A low marginal entropy without a conditional path certificate is a
   stopping condition. Existing moments provide demand, not this supply dichotomy.
3. **Coherent positive factorizations.** Optimize cut factors jointly with the
   displayed transition identities, measuring edges rather than factor ranks.
   A theorem realizing such factorizations with `B<A` would have the same numerical
   effect. The smallest falsification test is `L={000,100,101}`; failure of its
   prescribed gluing must be detected. Cutwise LP or rank improvement alone stops
   short of a circuit result. This is less mature than exact semantic quotienting.

## Validation and limitations

Run `python3 research/lower-bound-vantages/communication/data/check_semantic_quotients.py`.
The [stdlib checker](data/check_semantic_quotients.py) verifies both optimal cover
sizes, exhausts all 256 intermediate edge relations, and enumerates every path of
the counting example: four accepted words throughout, with path totals `4,8,4`
for the original, union quotient, and representative quotient. It proves no
asymptotic savings. Literature statements were checked against primary papers or
author/publisher records on 2026-10-06. No improved unrestricted coefficient,
efficient semantic compiler, or weighted DNNF pruning theorem is claimed.

[amarilli20]: ../sources.md#amarilli20
[bova16]: ../sources.md#bova16
[braverman-rao14]: ../sources.md#braverman-rao14
[bryant86]: ../sources.md#bryant86
[darwiche-marquis02]: ../sources.md#darwiche-marquis02
[faenza15]: ../sources.md#faenza15
[ggks20]: ../sources.md#ggks20
[gpw17]: ../sources.md#gpw17
[jain-klauck10]: ../sources.md#jain-klauck10
[kw90]: ../sources.md#kw90
[kw93]: ../sources.md#kw93
[paturi-simon86]: ../sources.md#paturi-simon86
[pich22]: ../sources.md#pich22
[reichardt11]: ../sources.md#reichardt11
[wigderson93]: ../sources.md#wigderson93
