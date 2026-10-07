# Reading and checking the formalization

Start with the statement of the result you need. The lower bounds count **positive-arity
gates**, including unary gates. Constants and input ports are free. Fan-out is unrestricted;
the signature and its interpretation describe the gate basis.

## Which theorem applies?

Write `L = 1 + pi / (3 arccos((1 + 2 sqrt(2))/4))`, approximately `4.56249768`.
Each asymptotic statement fixes a positive gap `epsilon` before choosing the input threshold.

| Computation model | Assumption on the family | Checked conclusion | Entry point |
| --- | --- | --- | --- |
| Exact deterministic circuits | Dense rectangle-free sets, `log K = o(n)` | `s > (L-epsilon)n` | [`lowerBound_gaussian`](../Frontier/Main.lean) |
| Existential verifiers | The same set assumptions | The same lower bound, uniformly in witness length | [`lowerBound_nondeterministic_gaussian`](../Frontier/Nondeterministic.lean) |
| Polynomial-size existential verifiers | The same assumptions and `s <= n^D`, with fixed `D` | `s > (L-epsilon)n + r`, where `r` counts reachable witness ports | [`lowerBound_nondeterministic_witnesses_gaussian`](../Frontier/Nondeterministic.lean) |
| Approximate deterministic circuits | Bias at most `2 b(n)` on every sufficiently large coordinate rectangle | Agreement at most `1/2 + b(n) + 2^(-gamma n)` below the size threshold | [`averageCase_gaussian`](../Frontier/AverageCase/Main.lean) |
| Randomized circuits | The same bias assumption; seed law independent of the input | The same average success bound and an input with success at most that bound | [`averageCase_randomized_gaussian`](../Frontier/Randomized.lean) |
| Bounded-error randomized circuits | The same assumptions and `b(n) -> 0` | Any fixed success probability above `1/2` on every input requires `s > (L-epsilon)n` | [`lowerBound_randomized_gaussian`](../Frontier/Randomized.lean) |

The randomized results allow arbitrary joint laws on any finite number of coin ports.
The bits need not be unbiased or mutually independent. The witness-sensitive result counts
distinct syntactically reachable witness inputs, not the declared witness length or the
number of times a port is used. It does not supply a witness-elimination algorithm.

The Gaussian **layout coefficient** is unconditional. Instantiating a circuit theorem still
requires its stated family hypothesis. In particular, rectangle-freeness supplies exact
hardness, whereas the randomized bounded-error argument uses the stronger bias hypothesis.
The cited explicit extractor constructions and their polynomial-time evaluation remain
external; the implications from their combinatorial guarantees are checked in Lean.

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
