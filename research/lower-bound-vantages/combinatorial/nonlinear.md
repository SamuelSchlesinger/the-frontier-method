# Nonlinear routes: weighted elimination and depth reduction

[Combinatorial comparison](index.md) · [Corpus](../index.md)

Both papers below concern ordinary `B2` DAGs with unrestricted depth and fanout,
counting binary internal gates. Unary normalization affects at most the output
gate, so their leading coefficients are comparable to our positive-arity count.

| Route | Verified mechanism and numerical statement | Contact with the frontier method |
|---|---|---|
| Golovnev–Kulikov weighted gate elimination [gk16weighted][gk16weighted] | Branch on degree-two equations; compare weighted circuit decrease with **logarithmic variety size**, not dimension. The proof uses XOR-layered circuits with measure `G+alpha*I`, then returns an ordinary `B2` bound | Already supplies entropy-sensitive nonlinear branching; retaining its variety hypotheses is essential |
| Golovnev–Kulikov–Williams depth reduction [gkw21][gkw21] | Theorem 1: every size-`s` circuit is an OR of at most `2^ceil(s/3.9)` 16-CNFs, using internal-gate branching with consistency conditions retained | Supplies exact terminals of bounded clause width; its exponent charges `s`, with no `-n` credit |

More precisely, call `f` an `(m,T)` quadratic disperser if it is nonconstant on
every common zero set of at most `m` degree-at-most-two polynomials over `F2`
having at least `T` points. Weighted elimination, Theorem 1, gives
`C(f) >= min{beta*(n-log2 T-1), 2m} - alpha*n`, provided its four branching
inequalities hold. The displayed choice `alpha=.535, beta=3.6513` satisfies them;
`m=1.83n, T=2^o(n)` therefore yields `3.1163n-o(n)`, strengthening the abstract's
rounded `3.11n` [gk16weighted][gk16weighted]. The variety-volume induction is an
existing method, not a new consequence of our restriction-surplus identity.

The depth-reduction paper's full version, Theorem 5.2, gives the explicit source
requirement: if `|f^(-1)(1)|>=2^(n-1)` and `f` is nonconstant on every zero set of
at most `1.3(1-epsilon)n` degree-at-most-16 polynomials having more than
`2^(epsilon*n)` points, then `s(f)>=3.9(1-epsilon)n-4`. Complementing `f` handles
the other density case. Its finer representation uses at most `ceil(s/3)` constraints,
each computed by a size-15 circuit; hence the degree and equation-count bounds.
This is an unconditional circuit compiler plus a disperser hypothesis, separate
from that paper's conditional De Morgan formula reduction [gkw21][gkw21].

**Comparison with `L`.** Neither `3.1163` nor the limiting `3.9` improves
`4.562497...`. In particular, `1/3.9 < A` is insufficient: `s/3.9` differs from
`A(s-n)`. With demand `2^(n-o(n))`, a hypothetical compiler charging
`(s-lambda*n)/3.9` would require `lambda>L-3.9=0.6624976789...` to improve `L`.
That compiler and its demand theorem are unproved. A nonlinear hybrid must also
justify frontier demand on the constrained varieties, or construct a target
dispersing them directly; sumset extraction alone supplies no such closure.

[gk16weighted]: ../sources.md#gk16weighted
[gkw21]: ../sources.md#gkw21
