# Algorithms, explicitness, and limits of transfer

[Corpus](../index.md) · [Restriction accounting](../combinatorial/index.md) ·
[Algebraic models](../algebraic/index.md)

These methods can change the target function, obtain a lower bound through an
algorithm, or diagnose the scope of an argument. Their consequences need not be a
larger coefficient for the same explicit function. In particular, a separation
for an exponential-time language is different from a lower bound for a
polynomial-time sumset extractor.

## Comparison

| Method | What supplies the contradiction | Contact with the frontier method |
|---|---|---|
| Counting, incompressibility, description length | Too few small descriptions for all truth tables | Establishes abundant hard objects; does not select a polynomial-time one or charge reused gates more accurately |
| Diagonalization and hierarchies | A simulation computes a language within a forbidden resource bound | Potential endpoint of an algorithmic extension; enumeration of small circuits by itself changes the explicitness class |
| SAT/#SAT algorithms to lower bounds | A sufficiently fast circuit algorithm plus a hierarchy theorem | Our constructive supply has a reciprocal algorithmic interpretation, but its linear-size regime is too narrow for the standard superpolynomial consequences |
| Learning to lower bounds; natural properties to learning | Efficient learners/hypotheses or constructive truth-table properties | May turn structural compression into another algorithmic output; query access, circuit class, and approximation model must be retained |
| Hardness versus randomness, hitting sets, PIT | Hard functions yield pseudorandomness; derandomization can imply lower bounds | A useful two-way test of representations, not a free amplification of a linear gate coefficient |
| Extractors, dispersers, additive combinatorics | A target forbids or balances the structured distributions a small representation generates | Already the demand engine; strengthening the source class is a concrete option when changing the compiler geometry |
| Hardness amplification, direct products, XOR lemmas | Hardness against prediction is amplified with a reconstruction argument | The expanded input length and reconstruction circuit cost affect the coefficient; ordinary block composition can destroy rectangle-freeness |
| Hardness magnification and self-reduction | A weak lower bound for a particular meta-computational problem implies a strong separation | The particular problem and promise parameters matter; five for an arbitrary explicit extractor is not automatically a magnification hypothesis |
| Natural proofs, relativization, algebrization, locality | A proposed mechanism is incompatible with specified simulations or pseudorandomness assumptions | Tests for stronger ambitions, not established obstructions to improving `4.562...` to five |

## Counting gives hard functions, not the missing compiler

A topologically ordered `s`-gate full-binary-basis circuit on `n` inputs has at
most `16^s (n+s+2)^(2s+1)` descriptions, allowing constants and an output choice.
Padding by redundant gates covers circuits of smaller size. Hence only
`2^O(s log(n+s))` of the `2^(2^n)` Boolean functions have such circuits. This is
the classical counting mechanism associated with Shannon [shannon49][shannon49];
the displayed loose bound follows by choosing each truth table and two predecessors.

The existence of functions needing exponential size is therefore compatible with
our difficulty at five. A lexicographic search for an incompressible truth table
does not run in polynomial time in `n`. A short uniform description also does not
imply small circuit size without a bound on the time to evaluate it.

Counting can still guide finite experiments: measure how many semantic transition
types a small paid circuit realizes, rather than counting all functions on its
frontier. To obtain a coefficient, turn that census into a theorem giving a
common exact representation with `log2 D <= B(s-n)+o(n)`. Counting abstract local
types independently would again ignore compatibility and circuit reuse.

## The exact algorithmic scale

For the current supply coefficient `A`, the gate-only counting exponent is
`alpha=A/(1+A)=1/L`. At `s=c*n`, it gives

```
2^((c/L+o(1))*n),
```

before taking the minimum with exhaustive search. Thus its size-only guarantee
beats `2^n` when `c<L`; at `c=5` it gives approximately `2^(1.095891*n)` and
brute force wins. The reachable-input version `min{m,A(s-m)}` can be better for
particular instances, but does not supply a universal saving at `s=5n,m=n`.

Williams's algorithm-to-lower-bound theorem instead asks for SAT speedups on
`n^k`-size circuits for every fixed `k`, with a superpolynomial saving over
`2^n` after polynomial overhead. A `2^(alpha*s)` algorithm does not meet that
hypothesis when `s=n^2`. This distinction is why the existing counting theorem
does not already imply `NEXP` lacks polynomial-size circuits
[williams13][williams13].

Two programs are consequently separate. Better **positive exact compilation**
can improve both our coefficient and counting. An algorithm using signed
contractions or cancellation could improve counting without a sound accepting
representation; its reciprocal lower bound would need a separate argument.
Randomized, deterministic, exact-counting, and decision guarantees must also be
kept distinct in any algorithmic reduction.

Learning offers another diagnostic. Fortnow--Klivans derive circuit lower bounds
from specified efficient learning algorithms, while Carmosino--Impagliazzo--
Kabanets--Kolokolova obtain learning algorithms from natural properties, including
uniform-distribution learning with membership queries for `AC^0[p]`
[fortnowklivans09][fortnowklivans09] [carmosino16][carmosino16]. Neither says that
our transition list is efficiently learnable from examples. A concrete extension
would discover a compact coherent quotient from circuit access, then specify
whether the learner can obtain that access in its stated query model.

## Hardness, pseudorandomness, and identity testing

The Nisan--Wigderson generator translates circuit hardness into pseudorandomness
with parameter losses from the design and reconstruction. Its role is not to
multiply a gate coefficient while leaving input length unchanged
[nisanwigderson94][nisanwigderson94]. Likewise, hardness amplification improves
prediction hardness only after accounting for the circuit that reconstructs a
predictor for the original function. The product-fiber counterexample in the
[combinatorial comparison](../combinatorial/index.md) shows why block composition
cannot simply be fed back into our existing rectangle demand.

Kabanets--Impagliazzo show that sufficiently strong identity-testing
derandomization implies a Boolean or arithmetic circuit lower bound
[kabanetsimpagliazzo04][kabanetsimpagliazzo04]. This is relevant to the arithmetic
extension, but the field, degree, and representation of the tested polynomial are
part of the premise. Testing Boolean truth tables modulo `x_i^2-x_i` is not the
same as formal polynomial identity testing. No general PIT derandomization or new
PIT consequence of the frontier theorem is claimed here.

## Strengthening the hard source class

Sumset extraction is especially well matched to splicing: two independently chosen
pieces combine by addition. Chattopadhyay--Liao supply the polylogarithmic-entropy,
polynomial-error construction already used for the draft's average-case bound;
Li supplies the logarithmic-entropy construction used in its exact instantiation
[chattopadhyayliao22][chattopadhyayliao22] [li23][li23]. Smaller entropy or error
improves the remainder or agreement guarantee. It does not change `A` once the
entropy threshold is already `o(n)`.

There is a precise obstacle to allowing arbitrary nonlinear coordinates on the
strength of the same black-box assumption. Chattopadhyay--Goodman--Gurumukhani,
Theorem 5.16, construct quadratic non-oblivious bit-fixing sources of entropy
`n-O(n/log log n)` that are almost distance one from **every convex mixture** of
sumset sources whose two summands have entropy `c log n`, for any fixed `c>0`
[chattopadhyaygoodmangurumukhani24][chattopadhyaygoodmangurumukhani24]. A
non-oblivious bit-fixing source has uniform independent good bits and other bits
that are functions of them; here those functions are quadratic.

This refutes the proposed generic reduction through convex mixtures of sumset
sources. It does not say that every particular sumset extractor fails on those
sources, nor that a specially chosen extractor cannot satisfy both properties.
It also concerns polynomial-image sources; uniform points of a polynomial
zero-set are a different definition. The non-oblivious sources used in that
result belong to both relevant classes.

The useful alternative is **source--compiler co-design**. First identify the
structured sources or varieties forced by the failed restriction cases. Then
seek dispersion/bias on exactly that class, together with a compiler that pays
for its nonlinear coordinate construction. The weighted gate-elimination and
depth-reduction precedents are discussed in the
[combinatorial comparison](../combinatorial/index.md). A stronger extractor alone
is insufficient: its entropy range must intersect the range produced by that
specific simplification theorem.

For additive-combinatorial ideas such as energy or approximate-group structure,
the same rule applies. A large additive energy is not itself a sound accepting
sumset, and an inverse theorem that loses a linear fraction of dimension can
consume the entire numerical gain. The relevant proposed lemma must yield valid
pieces, retain density or bias after conditioning, and bound their total cost.

## Magnification and barriers: correct questions at the correct scale

Oliveira--Santhanam magnify weak lower bounds for specified versions of MCSP,
time-bounded Kolmogorov complexity, and other problems. For a truth-table problem,
the input length is `N=2^n`, not `n`; gap parameters and the precise circuit or
formula model are decisive [oliveirasanthanam18][oliveirasanthanam18]. We have not
shown the required rectangle/sumset demand for such a promise problem. There is
no valid step from `5n` for our extractor to a superpolynomial lower bound merely
by invoking magnification.

Pich proves that the approximation method localizes in a sense that creates a
barrier to specified magnification approaches [pich22][pich22]. An appropriate
test here is to add small-fan-in oracle gates and see whether the proposed demand
and supply continue to hold with the claimed prices. Our degree and gate-cost
accounting changes with arity, so neither immunity to that barrier nor coverage
by it has been proved. This is a diagnostic task if a magnification target is
chosen, not a reason to halt the search for a better constant.

Razborov--Rudich's natural-proofs barrier concerns constructive, sufficiently
large properties useful against a circuit class containing sufficiently strong
pseudorandom functions, under the corresponding hardness assumption
[razborovrudich97][razborovrudich97]. It is not a prohibition on explicit linear
lower bounds. To classify a frontier extension, check truth-table constructivity,
largeness, and the actual size class separately. Quantifying over all partitions
and large subsets does not by itself give a polynomial-time truth-table test.

Relativization and algebrization similarly have specific meanings. Baker--Gill--
Solovay exhibit conflicting oracle worlds for `P` versus `NP`; Aaronson--
Wigderson strengthen the diagnostic by allowing algebraic extensions of oracles
[bakergillsolovay75][bakergillsolovay75] [aaronsonwigderson09][aaronsonwigderson09].
Neither establishes a ceiling of five for binary circuits. Conversely, using
Gaussian geometry or Lean does not by itself evade either barrier. A simulation
or oracle analysis must establish the claimed relationship.

## Decision

The most useful contribution of this family is to match **the next compiler** to
**the next target property**. Continue the constant-improvement program with the
existing target while testing paid affine compression and restriction coverage.
Treat nonlinear source hardness as a separate, well-specified route, and retain
algorithmic gains even when they lack a reciprocal support lower bound. Broad
complexity-class consequences require additional hypotheses not supplied here.

[aaronsonwigderson09]: ../sources.md#aaronsonwigderson09
[bakergillsolovay75]: ../sources.md#bakergillsolovay75
[carmosino16]: ../sources.md#carmosino16
[chattopadhyaygoodmangurumukhani24]: ../sources.md#chattopadhyaygoodmangurumukhani24
[chattopadhyayliao22]: ../sources.md#chattopadhyayliao22
[fortnowklivans09]: ../sources.md#fortnowklivans09
[kabanetsimpagliazzo04]: ../sources.md#kabanetsimpagliazzo04
[li23]: ../sources.md#li23
[nisanwigderson94]: ../sources.md#nisanwigderson94
[oliveirasanthanam18]: ../sources.md#oliveirasanthanam18
[pich22]: ../sources.md#pich22
[razborovrudich97]: ../sources.md#razborovrudich97
[shannon49]: ../sources.md#shannon49
[williams13]: ../sources.md#williams13
