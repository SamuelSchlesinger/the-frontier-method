# Proof complexity: certificates for frontier compression

[Parent](index.md) · [Corpus](../index.md)

Proof complexity offers tools for certifying which boundary assignments can coexist
and exposing limitations of local reasoning. Its most plausible contribution here is
a **sound compiler for cheaper semantic interfaces**. Hard refutations of unrelated
constraint systems do not establish circuit-size lower bounds. No improved coefficient is proved below.

## The transfer that would count

Fix the corpus model: a deterministic Boolean gate DAG, full binary basis,
arbitrary fan-out, `s` positive-arity gates, and `n` ordinary inputs. Its gate
equations are total functional relations; acyclicity gives one complete trace per
input. In contrast, a bounded-arity constraint network may use arbitrary relations,
have cycles, and have zero or many completions. Forgetting that distinction loses
the semantic information a stronger supply theorem might exploit.

**Proposed supply bridge.** For every such circuit, construct compatible transition
codes, with proof certificates if useful, whose total charged transition count is
`D <= 2^(B(s-n)+o(n))`, for a fixed `B < A = 0.280701937...`. Codes must preserve
accepted inputs and the frontier splicing property. Equality of two codes must
justify replacement in every relevant continuation, and that equivalence must
survive transition updates. Certifying individual implications is insufficient.
Existing demand then gives coefficient `1+1/B`; `B=1/4` gives five. No cited proof system supplies this bridge.

A different bridge would associate an unsatisfiable formula `F(C,f)` to **every** small
circuit computing the target, bound its proof resource from `s,n`, and prove an
incompatible lower bound uniformly over these formulas. Encoding `C(x) != f(x)`
does not supply the upper bound: proving equivalence can be difficult even when both
circuits are small. Target encoding, extensions, and simulation constants must be charged.

## Resolution: width, space, and size

Resolution derives clauses by eliminating a complementary pair of literals.
For an unsatisfiable CNF on `N` variables, let `w0` be its initial width, `W` its
minimum refutation width, and `S` its minimum DAG refutation size. The
Ben-Sasson–Wigderson tradeoff yields
`S >= exp(Omega((W-w0)^2/N))`; tree-like and general DAG proofs have different
tradeoffs [bw01][bw01]. The hidden constant is not a numerical improvement to `A`.

Atserias–Dalmau characterize width through an existential pebble game and show
that minimum clause space is at least `W-w0` [ad08][ad08]. Clause space counts
simultaneously stored clauses, not stored bits or frontier signals. One wide
clause can mention many variables. Conversely, many clauses can describe the same
small interface; multiplying clause space by an unstated word size is not free.

**Transfer opportunity.** Use local-consistency games to exclude unrealizable boundary
assignments or certify a forgetting rule. To improve supply, the remaining assignments
must admit fewer compatible transition codes on every required circuit. Width hardness
for arbitrary CSPs can diagnose failure of a bounded-width simplifier, but gives neither
a universal compression algorithm nor a lower bound for the original Boolean function.
Recomputation may destroy a one-pass representation or enlarge the transition count.

## A proved encoding check: fixing inputs makes circuit propagation easy

For each gate `y = h(u1,...,uk)`, `k <= 2`, encode its relation by one clause
excluding each forbidden truth-table row. Fix a complete ordinary-input assignment
and add the unit literal asserting the **wrong** output value. The resulting CNF
has a DAG resolution refutation of width at most three using at most `2s+1`
resolution inferences, where input and constant units are axioms.

**Proof.** Process gates topologically. For the already known input values, the
clause excluding the wrong output resolves with at most `k` input units to give
the correct output unit. Reuse derived units wherever needed. Finally resolve the
output unit with its opposite. Sum `k <= 2` over positive-arity gates; zero-arity
gate clauses are already units. This is a mathematical proof, not a Lean theorem.

This standalone Python checks all 74 truth-table/input pairs of arity zero, one,
or two. It was run during authoring; the DAG statement follows by induction above.

[Reproducible gate-propagation check](data/check_propagation.py).


This does not make the unconditioned circuit-output CNF easy. Hardness must survive
leaving many inputs free; conditioning cannot be silently removed. More directly,
for **every unsatisfiable CNF** `F`, the function `x -> F(x)` is identically zero and
has a zero-gate circuit here, since constants are free. Refutation complexity of the
presentation `F` cannot lower-bound the minimum circuit computing its satisfaction function.

## Polynomial calculus and Nullstellensatz

Over a specified field, include Boolean axioms `z^2-z=0`. Polynomial calculus
(PC) derives equations by linear combinations and multiplication by variables;
a refutation derives `1=0`. Standard size counts monomial occurrences, while degree
bounds intermediate polynomials. Impagliazzo–Pudlák–Sgall connect degree lower
bounds to monomial-size lower bounds [ips99][ips99]. Nullstellensatz instead uses
a static identity `sum_i q_i p_i = 1`; its certificate degree and representation
must be specified separately [gp18][gp18]. Neither monomial count nor degree is
the size of an unrestricted arithmetic circuit computing the certificate.

**Transfer opportunity.** Eliminate internal gate variables and certify equations
on a boundary, then count their actual Boolean solutions or continuation classes.
A useful result must prove that this count saves `Omega(s-n)` bits beyond the
existing layout bound, with compatible updates. Low equation degree alone says
nothing about that count: `z_i^2-z_i=0` for `b` independent boundary variables
has degree two and permits all `2^b` states. Field arithmetic, cancellation,
and polynomial identities are not positive splicing rules.

IPS, the Ideal Proof System, does provide a genuine reverse connection:
superpolynomial circuit-size lower bounds for its Boolean refutations imply
algebraic circuit lower bounds separating VP and VNP [gp18][gp18]. This uses
arithmetic circuits as proof objects; it is not a transfer from ordinary PC
degree hardness to the present Boolean `4.562497n` coefficient.

## SOS, Positivstellensatz, and cutting planes

Over the reals, an SOS refutation of equations `p_i=0` can use
`-1 = sum_j q_j^2 + sum_i h_i p_i`; inequalities require specifying the allowed
nonnegative multipliers and products. Degree, monomial size, coefficient bit
length, and circuit representation are different resources. Grigoriev's knapsack
examples demonstrate linear-degree Positivstellensatz hardness and sensitivity
to the instance's numerical parameters [grigoriev01][grigoriev01].

Lasserre/SOS lower bounds can be witnessed by locally consistent moment data;
Schoenebeck gives linear-level gaps for specified random CSP families
[schoenebeck08][schoenebeck08]. Such data need not come from a global probability
distribution on solutions. **Transfer opportunity:** use a dual certificate to
test an asserted local compression inequality. **Missing step:** convert the
result into actual boundary support or an actual nonnegative, coherent sweep.
Pseudoexpectation “entropy” cannot replace the true transition masses in the
[existing moment theorem](../../communication/README.md).

Cutting planes derives integer inequalities using nonnegative integer combinations and
rounding. Its proof length, rank, and coefficient restrictions must be kept
separate. Pudlák's lower bounds use monotone computation and interpolation
[pudlak97][pudlak97]. A short inequality may encode a large boundary sum; counting
it as one state hides both coefficient cost and the number of possible values.
A usable transfer must bound those values or continuation classes and pay for
combining inequalities across cuts; proof rank alone does not do this.

## Interpolation, automatization, and definitions

Feasible interpolation extracts a separating computation from a refutation of
`A(x,y) AND B(x,z)`. Consequently, a lower bound for the extracted computation
can force large proofs; reversing this implication is invalid. Krajíček's
randomized version can produce monotone circuits with local oracles
[krajicek18][krajicek18]. These oracles, randomness, and monotonicity restrictions
must not disappear in a claimed full-basis circuit transfer.

**Possible use:** prove that short interface certificates yield communication
messages satisfying the exact continuation property above. The compiler must
account for proof DAG reuse, both output classes, error, and message multiplicity.
Merely extracting a protocol for a different search relation does not suffice.

Proof existence differs from finding proofs. Polynomial-time resolution automatization
would imply `P=NP` [am20][am20]. This does not prohibit efficient search on a proved
special subclass; existential compression certificates alone give no faster #SAT algorithm.

Definitions such as `z = h(u,v)` introduce precisely the kind of shared gate
variables already present in the circuit encoding. A lower bound established
without these definitions need not survive their addition. Any extension rule
must carry its gate cost, occurrences, and effect on `s-n`; unrestricted semantic
axioms cannot be treated as free evidence. Conversely, prohibiting all auxiliary
variables could exclude the circuit compiler itself. This obligation applies
before transferring bounds for resolution, PC, SOS, or stronger proof systems.

## Decision and next test

Prioritize proof-certified interface forgetting, checking continuation equivalence and
transition coherence on small full-basis DAGs. Stop a rule when its codes merge states
with different continuations, or accumulated cost restores the old exponent.
Proof hardness for arbitrary local relations is useful for falsification; advancement
requires the universal supply bridge or proof-resource sandwich above. Neither is established here.

[ad08]: ../sources.md#ad08
[am20]: ../sources.md#am20
[bw01]: ../sources.md#bw01
[gp18]: ../sources.md#gp18
[grigoriev01]: ../sources.md#grigoriev01
[ips99]: ../sources.md#ips99
[krajicek18]: ../sources.md#krajicek18
[pudlak97]: ../sources.md#pudlak97
[schoenebeck08]: ../sources.md#schoenebeck08
