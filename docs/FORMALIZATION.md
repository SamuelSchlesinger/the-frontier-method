# Reading and checking the formalization

Start with the statement of the result you need. The lower bounds count **positive-arity
gates**, including unary gates. Constants and input ports are free. Fan-out is unrestricted;
the signature and its interpretation describe the gate basis.

## Which theorem applies?

Write `A = (3/pi) arccos((1 + 2 sqrt(2))/4)` and `L = 1 + 1/A`, approximately `4.56249768`.
Each asymptotic statement fixes a positive gap `epsilon` before choosing the input threshold.
The exact set bounds require a fixed finite alphabet with at least two symbols. Here
"dense" means `n log |U| - log |S_n| = o(n)`.

| Computation model | Assumption on the family | Checked conclusion | Entry point |
| --- | --- | --- | --- |
| Exact deterministic circuits | Dense rectangle-free sets, `log K = o(n)` | `s > (L-epsilon)n` | [`lowerBound_gaussian`](../Frontier/Main.lean) |
| Existential verifiers | The same set assumptions | The same lower bound, uniformly in witness length | [`lowerBound_nondeterministic_gaussian`](../Frontier/Nondeterministic.lean) |
| Polynomial-size existential verifiers | The same assumptions and `s <= n^D`, with fixed `D` | `s > (L-epsilon)n + r`, where `r` counts reachable witness ports | [`lowerBound_nondeterministic_witnesses_gaussian`](../Frontier/Nondeterministic.lean) |
| Approximate deterministic circuits | Bias at most `2 b(n)` on every sufficiently large coordinate rectangle | Agreement at most `1/2 + b(n) + 2^(-gamma n)` below the size threshold | [`averageCase_gaussian`](../Frontier/AverageCase/Main.lean) |
| Randomized circuits | The same bias assumption; seed law independent of the input | The same average success bound and an input with success at most that bound | [`averageCase_randomized_gaussian`](../Frontier/Randomized.lean) |
| Bounded-error randomized circuits | The same assumptions and `b(n) -> 0` | Any fixed success probability above `1/2` on every input requires `s > (L-epsilon)n` | [`lowerBound_randomized_gaussian`](../Frontier/Randomized.lean) |
| Linear maps over finite fields | A totally regular `N × N` matrix; any binary gate basis | `s > (L-epsilon)N`, uniformly over finite fields | [`linear_finite_gaussian`](../Frontier/Linear/Main.lean) |
| Linear maps over infinite fields | A totally regular matrix; binary gates interpreted by polynomials | `s > (L-epsilon)N` | [`linear_polynomial_gaussian`](../Frontier/Linear/Main.lean) |
| Arithmetic circuits for Cauchy maps | The specified Cauchy matrix over a characteristic-zero field | More than `(L-epsilon)N` additions and multiplications | [`arith_cauchy_gaussian`](../Frontier/Linear/Main.lean) |
| Scalar polynomial circuits | Every input occurs; mixed-Hessian demand at least `rho n`, with `rho >= 0`; binary polynomial gates over any field | `s > (1 + rho/A - epsilon)n` | [`Arithmetic.lowerBound_hessian_gaussian`](../Frontier/Arithmetic/LowerBound.lean) |
| Determinant circuits | Formal computation of the `n × n` determinant; binary polynomial gates over any field | `s > (1 + 1/(4A) - epsilon)n²`, with leading coefficient about `1.89062442` | [`Arithmetic.lowerBound_determinant_gaussian`](../Frontier/Arithmetic/Determinant.lean) |
| Nonlinear MDS maps | Any `N` of the `2N` input/output coordinates recover the input; finite nontrivial alphabet; any binary basis | `s > (L-epsilon)N` | [`mds_gaussian`](../Frontier/Boundary/MDS.lean) |
| Circuits with aggregate gates | Dense rectangle-free sets; ordinary fan-in two; `k` special gates aggregate in a finite commutative monoid `T`, with `k log \|T\| = o(n)` | More than `(L-epsilon)n` ordinary positive-arity gates | [`lowerBound_aggregate_gaussian`](../Frontier/Ledger/Main.lean) |
| Smooth decomposable union/product DAGs | Rectangle-free accepted set `S`; `1 < K <= \|S\|`; binary products, possibly overlapping union branches | `\|S\| <= (K-1)² E + (K-1)³ P`, where `E` counts union edges and `P` product nodes | [`Decomposable.ncard_le`](../Frontier/Decomposable.lean) |

Linear-map computation is equality of functions. The scalar polynomial and determinant
theorems instead concern the formal polynomial `wirePolynomial`; over a finite field,
agreement on all field-valued inputs does not imply equality of polynomials. They allow
every field characteristic, including two. The Cauchy arithmetic instance above needs
characteristic zero; [`cauchyZMod_gaussian`](../Frontier/Linear/Main.lean) supplies a separate
prime-field instance for primes `q >= 2N`.

The general [`lowerBound_ledger`](../Frontier/Ledger/LowerBound.lean) allows any checked
ledger in a finite commutative monoid `M` with `log |M| = o(n)`. It counts the positive-arity
gates of the erased program; special gates are charged through the ledger instead.
The decomposable bound is finite counting, not an asymptotic circuit coefficient, and does
not require disjoint union branches.

The randomized results allow arbitrary joint laws on any finite number of coin ports.
The bits need not be unbiased or mutually independent. The witness-sensitive result counts
distinct syntactically reachable witness inputs, not the declared witness length or the
number of times a port is used. It does not supply a witness-elimination algorithm.

The Gaussian **layout coefficient** is unconditional. Instantiating a circuit theorem still
requires its stated family hypothesis. In particular, rectangle-freeness supplies exact
hardness, whereas the randomized bounded-error argument uses the stronger bias hypothesis.
The cited explicit extractor constructions and their polynomial-time evaluation remain
external; the implications from their combinatorial guarantees are checked in Lean.
For exact bounds, [`FlatSumsetBias.rectangleBias`](../Frontier/AverageCase/Extractor.lean)
followed by [`RectangleBias.rectangleFree`](../Frontier/AverageCase/Bias.lean) gives
rectangle-free Boolean fibers when `0 < K` and the bias is below one. Fiber density must
still be supplied separately.

## Work through a circuit

[`examples/Compiler.lean`](../examples/Compiler.lean) formalizes the paper's three-gate
circuit `a = x₁ xor x₂`, `b = a xor x₃`, `c = a or b`. It constructs the circuit, identifies
its accepted inputs, counts the compiled graph, and checks a frontier before any inputs
are read. Run it after the library build:

```sh
lake env lean -DwarningAsError=true examples/Compiler.lean
```

CI checks this file as a client of the library. Its small finite computations document the
compiler's conventions; the general compiler exactness theorem supplies the semantic step.

## Follow the exact lower-bound proof

1. [`Rectangle.lean`](../Frontier/Rectangle.lean) defines coordinate rectangles and proves
   that a large rectangle-free set must depend on almost every input coordinate.
2. [`Sweep.lean`](../Frontier/Sweep.lean) proves the abstract counting inequality. Equal
   boundary messages let a prefix and a suffix be spliced; rectangle-freeness limits how
   many accepting inputs a transition can account for.
3. [`Compiler.lean`](../Frontier/Compiler.lean) gives exact local constraints for a circuit,
   including copies of shared wires. Positive-arity size and reachable inputs control
   the graph's cycle rank. Parallel edges are counted separately.
4. [`Reduction.lean`](../Frontier/Reduction.lean) combines the support and counting facts:
   a small deciding circuit would give a graph of small cycle rank whose every layout
   nevertheless has a wide frontier.
5. [`Layouts.lean`](../Frontier/Layouts.lean) supplies a layout of bounded width.
   [`Demand.lean`](../Frontier/Demand.lean) isolates the final real inequality, and
   [`LowerBound.lean`](../Frontier/LowerBound.lean) combines the two sides.
   [`Main.lean`](../Frontier/Main.lean) substitutes the proved Gaussian coefficient.

In [`Layouts/Gaussian.lean`](../Frontier/Layouts/Gaussian.lean), the private
`SampleConcentration` interface records the grid, window, and tail estimates.
`exists_concentrated_sample` proves their simultaneous existence; `exists_good_sample`
then converts them to a median layout. In
[`Ledger/LowerBound.lean`](../Frontier/Ledger/LowerBound.lean), the private
`logb_le_of_count`, `step_width_le`, and `card_vtx_le` lemmas isolate the finite estimates
used by the final asymptotic comparison.

The graph coefficient `A` bounds width in terms of cycle rank. The cubic coefficient `p`
bounds width in terms of the number of cubic vertices. Compression gives `A = 2 p`.
Consequently the gate coefficient is `1 + 1/A = 1 + 1/(2 p)`; the two graph coefficients
should not be substituted for each other without this factor.

In Lean, `∀ᶠ n in atTop, ...` means that there is a threshold after which the statement
holds for every `n`. Quantifiers inside it are uniform: in these main theorems the threshold
does not depend on the later choice of basis, interpretation, circuit, witness length, or
coin distribution. The fixed polynomial exponent in the witness theorem comes before it.

## Follow the two extensions

[`Projection.lean`](../Frontier/Projection.lean) existentially hides witness ports without
changing the graph. [`Nondeterministic.lean`](../Frontier/Nondeterministic.lean) retains the
negative reachable-witness term in its cycle rank. The polynomial size assumption makes
the logarithmic graph overhead sublinear; discarding it in favor of an error proportional
to the graph size would not establish the stronger witness charge.

Randomization has three separate interfaces:

- [`Randomized/Basic.lean`](../Frontier/Randomized/Basic.lean): arbitrary nonnegative
  measurable payoffs and independent measures. Tonelli swaps the two averages. Probability
  measures give the fixed-seed and bad-input consequences, for any correctness relation.
- [`Randomized/Circuit.lean`](../Frontier/Randomized/Circuit.lean): uniform Boolean agreement
  and a black-box deterministic circuit bound. [`Restriction.lean`](../Frontier/ForCslib/Restriction.lean)
  fixes coin ports using free constants and proves exact preservation of size and fan-in.
- [`Randomized.lean`](../Frontier/Randomized.lean): the layout, Gaussian, polynomial-error,
  and bounded-error asymptotic corollaries. These use the average-case theorem, independently
  of the existential-witness argument.

A fixed seed can preserve average success under a specified input distribution. This does
not give a seed that works on every input. The argument is the standard averaging direction
of Yao's principle, not the minimax equality; see
[Blum and Blum, Section 5.4](https://www.cs.cmu.edu/~avrim/451f06/lectures/lects1-10.pdf).

## What verification establishes

`lake build --wfail` checks the Lean development. `lake env lean scripts/Audit.lean`
checks the allowed axiom dependencies of the named principal results. Neither command
alone detects an unintended weakening of a theorem statement.

Comparator adds a separate comparison against an immutable reviewed reference, including
the definitions used in theorem statements, and replays the exported proof dependencies
through Lean's kernel. A successful check establishes the formal propositions relative to
the permitted axioms and trusted reference. Matching those propositions to an informal
mathematical claim still requires reading the hypotheses, model, and quantifier order above.

Finite Python experiments check their enumerated cases and executable implementations.
They are useful regression checks, but do not establish asymptotic theorems or the runtime
claims that the paper identifies as unformalized.
