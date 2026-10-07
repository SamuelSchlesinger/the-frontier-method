# The Frontier Method

A self-contained, machine-checked account of circuit lower bounds from graph layouts.

The [formalization guide](docs/FORMALIZATION.md) maps the computation models to their
precise hypotheses, explains the proof route, and distinguishes the verification guarantees.
The [Comparator harness](verification/comparator/README.md) checks public theorem statements
against a pinned reference and replays their proof dependencies through Lean's kernel.

**Theorem.** Fix `r ≥ 2` and `A > 0`. Assume that graphs of maximum degree `r + 1` have layouts
whose frontiers carry at most `(A + o(1)) β₁ + o(|V|)` edges, where `β₁` is the cycle rank.
Let `U` be a finite alphabet with `|U| ≥ 2`, and let `S_n ⊆ U^n` be `K_n`-rectangle-free sets
with `log K_n = o(n)` and density defect `n log |U| - log |S_n| = o(n)`.
Then, for every fixed `ε > 0`, every circuit with `s` inner gates of
fan-in at most `r` (gates of positive arity; constants are free), over *any* basis on `U`,
deciding `S_n` satisfies

```
(r - 1) s > (1 + 1/A - ε) n        for all large n.
```

The layout bound is proved for subcubic graphs with `A = (3/π) arccos((1 + 2√2)/4) ≈ 0.2807`
(Gaussian edge scores), so circuits of fan-in two need more than `(L - ε) n` gates with
`L = 1 + 1/A ≈ 4.5625`, and in particular `(4 - ε) n`. The same frontiers give:

* **Explicit sets**: the fibers of sumset dispersers are rectangle-free, so the bound applies to
  balanced sumset dispersers (`Frontier.lowerBound_sumsetDisperser`). The paper obtains an
  explicit Boolean language in P from Xin Li's [sumset-extractor construction](https://arxiv.org/abs/2303.06802).
  This construction and its polynomial-time evaluation are external to the formalization.
* **Average-case hardness**: a one-bit sumset extractor with error `b_n` and
  entropy threshold `o(n)` has agreement at most `1/2 + b_n + 2^(-Ω_ε(n))` with every
  deterministic binary circuit of size at most `(L - ε)n`, for each fixed `ε > 0`.
  A weighted frontier lemma partitions an unambiguous program's accepted set into large
  rectangles and a small residual set. Its weighted form handles arbitrary input distributions
  through min-entropy, asymmetric rectangle thresholds, and a shared exceptional measure.
  Lean checks the coherent-sweep weighted inequality, the uniform circuit theorem
  (`Frontier.averageCase`, `Frontier.averageCase_abs`), and its flat-source sumset instantiation
  (`Frontier.averageCase_sumset`). The [Chattopadhyay–Liao extractor, Theorem 1](https://eccc.weizmann.ac.il/report/2021/147/revision/1/download/)
  gives an explicit language in P with agreement at most `1/2 + n^(-Ω(1))`: its entropy
  threshold is polylogarithmic and its error polynomially small. Lean checks the implication
  from such error bounds (`Frontier.averageCase_sumset_polynomial`); the construction is external.
  The explicit program partition and general distributional
  packing theorem remain paper proofs. The exponential remainder requires a fixed gap below `Ln`.
* **Randomized circuits**: the same average-case bounds hold for any number of random input
  ports with any joint distribution independent of the ordinary input
  (`Frontier.averageCase_randomized_gaussian`, `Frontier.averageCase_randomized_sumset_polynomial`).
  Some input has success probability at most the same bound; therefore any fixed success
  probability above `1/2` on every input requires more than `(L - ε)n` gates when the
  extractor error vanishes (`Frontier.lowerBound_randomized_gaussian`).
  The general transfer handles arbitrary measurable correctness relations and independent
  input and seed distributions, including infinite support (`Frontier.Randomized.success_le_of_class`).
  It uses average-case bias, a stronger hypothesis than rectangle-freeness alone.
* **Nondeterministic circuits**: the same coefficient holds for verifier circuits, uniformly
  in the number of existential witness inputs (`Frontier.lowerBound_nondeterministic_gaussian`).
  The gate count includes every positive-arity verifier gate; the input count includes only
  ordinary inputs. For every fixed `D`, a binary verifier with `s ≤ n^D` satisfies
  `s > (L - ε)n + r`, where `r` counts distinct witness inputs reachable from its output
  (`Frontier.lowerBound_nondeterministic_witnesses_gaussian`). Unused witnesses do not count.
* **Signal capacity**: the proved frontier inequality can charge distinct circuit signals
  instead of their repeated edge copies (`Frontier.Compiler.ncard_accepted_le_signals`).
  This supplies a finer capacity theorem; improving the numerical coefficient still requires
  a stronger signal-layout bound.
* **Every fixed fan-in**: Gaussian vertex ordering and multigraph compression give
  `LayoutBound d a_d` for every fixed `d ≥ 3`, with
  `a_d = 3d/(2d-3) · arccos(2√(d-1)/d)/π < 3/4`
  (`Frontier.layoutBound_degree`). Thus
  `(r-1)s > (1 + 1/a_(r+1) - ε)n` (`Frontier.lowerBound_degree`).
  At fan-in three this gives `s > (7/4 - ε)n`; at fan-in four the coefficient is
  approximately `1.092760448`. The binary median-edge coefficient `L` above is sharper.
  The checked graph proof counts parallel edges throughout; its per-edge estimate is
  `cutwidth ≤ arccos(2√(d-1)/d)/π · |E| + o(|V|)`
  (`Frontier.Gaussian.multigraph_vertexLayout_bound`). For comparison, a spanning tree gives
  `cutwidth(G) ≤ β₁(G) + d floor(log₂ |V|)` in maximum degree `d`, hence `LayoutBound d 1`.
  Thus `(r - 1)s > (2 - ε)n` for every fixed fan-in `r ≥ 2`
  (`Frontier.layoutBound_one`, `Frontier.lowerBound_all_fanIn`). No optimality or priority
  claim is made for the higher-fan-in constants.
* **Decomposable representations**: a smooth DNNF with `e` union edges and `v` binary product
  nodes representing a `K`-rectangle-free set `S`, with `K ≥ 2` and `|S| ≥ K`, satisfies
  `|S| ≤ (K-1)^2 e + (K-1)^3 v` (`Frontier.Decomposable.ncard_le`). Union branches may overlap.
  The paper deduces DNNF size `2^(n-o(n))` for dense families with `log K = o(n)`, and
  `2^(n-O(log n))` for the cited extractor family.
* **Mixed input-output recovery**: the product of two complementary mixed-observation fiber
  sizes bounds the inputs sharing a frontier message
  (`Frontier.Compiler.pow_le_cutSignals_mul_fibers`). Any finite-alphabet map whose graph
  code is MDS inherits the binary coefficient `L` and every fixed fan-in coefficient above
  (`Frontier.lowerBound_mds`, `Frontier.mds_gaussian`, `Frontier.mds_degree`). This includes totally regular maps
  and their nonlinear variants under coordinatewise alphabet permutations.
* **Linear maps and arithmetic circuits**: circuits computing a totally regular map `x ↦ M x`,
  over finite fields with any basis and over infinite fields with polynomial operations, need
  `(L - ε) N` gates; over every field of characteristic zero, arithmetic circuits computing the
  Cauchy map need `(L - ε) N` additions and multiplications (`Frontier.lowerBound_linear`,
  `Frontier.arith_cauchy_gaussian`). The displayed Cauchy matrices also work over prime fields
  of order `q ≥ 2N` (`Frontier.cauchyZMod_gaussian`). The general-degree coefficients also
  apply (`Frontier.linear_finite_degree`, `Frontier.linear_polynomial_degree`).
* **Scalar polynomials**: every compiled circuit cut bounds the mixed-Hessian rank across
  its input partition, over any field (`Frontier.Arithmetic.rank_mixedHessian_le_cut`).
  If all `N` variables occur formally and every input order has a prefix with rank at
  least `ρ N` at some evaluation point, a fan-in-two polynomial circuit needs more than
  `(1 + ρ/A - ε) N` inner gates for large `N`
  (`Frontier.Arithmetic.lowerBound_hessian_gaussian`). The point can depend on the order.
  Formal polynomial equality is required, including over finite fields. For the determinant,
  every input order has a prefix and permutation-matrix evaluation with mixed rank at least
  `n²/4 - 3n` (`Frontier.Arithmetic.hessianDemand_determinant`). This gives more than
  `(1.8906244197… - ε) n²` gates for all sufficiently large `n`, over every field
  (`Frontier.Arithmetic.lowerBound_determinant_gaussian`). Polynomial-multiplication
  demand remains open in this development.
* **Gates of unbounded fan-in**: the bound survives special gates with a *ledger* in a monoid `M`
  with `log |M| = o(n)`, for instance `o(n)` unbounded AND, OR, parity, or fixed-modulus count gates
  (`Frontier.lowerBound_ledger`, `Frontier.lowerBound_aggregate_gaussian`). The proof charges
  only the ordinary gates.

The exact and uniform average-case lower bounds, arithmetic instantiations, and layout theorem
are proved
with no `sorry`, using only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`),
in about 15,000 lines of Lean. The accompanying paper also gives a deterministic #SAT algorithm
for circuits of fan-in two with `s` positive-arity gates, running for every fixed `η > 0` in
time and space `O*(2^((1/L + η) s))`, where `1/L = 0.2191781936...`. Here `O*` suppresses
polynomial factors in the full circuit encoding and the number of inputs. With `m` inputs
reachable from the output, the sharper time bound is
`O*(2^(min(m, A(s-m)) + ηs))`. With a finite, efficiently evaluable ledger, the algorithm takes
`|M|^O(1) O*(2^((1/L + η) s_ord))`; this allows `k` unbounded AND/OR/parity/fixed-modulus gates
at an additional `O(k)` cost in the exponent.
For fan-in three, the degree-four layout gives time and space
`O*(2^((4/7 + η)s))`, with the sharper bound
`O*(2^(min(m, (2/5)(2s-m)) + ηs))`.
For every fixed fan-in `r`, the new coefficient gives gate exponent
`(r-1)a_(r+1)/(1+a_(r+1)) + η`, with input-sensitive exponent
`min(m, a_(r+1)((r-1)s-m)) + ηs`.

The deterministic cubic-layout construction uses fixed-accuracy discretization and conditional
expectations, taking `f(ξ) h^3 polylog(h)` time on an `h`-vertex cubic graph; the polynomial degree
is independent of accuracy. The paper also gives
a tree-limit calculation showing that the current local Gaussian straddling estimate is sharp.
The algorithms and their complexity bounds, this limiting calculation, the random-set existence
argument, the explicit program partition and general distributional packing bounds, and the
branching-program discussion are not formalized. The DNNF smoothing conversion is also a
paper proof; the finite threshold theorem is checked for the actual smooth union/product DAG.

The new boundary results are checked in Lean as well:

* Signal cuts are exactly cuts of a signal hypergraph and have submodular cardinality.
  Transition encodings can replace wire counts; for linear constraints, feasible syndromes
  form `im L ∩ im R`, with the exact matroid-connectivity dimension.
* Pruning a coherent sweep to selected transitions preserves splicing. Discarded uniform
  probability mass `δ` contributes at most `δ/2` to the agreement bound.
* Optimizing the pruning cost caps each transition's charge by the mass of its inputs.
  Fractional moments give Renyi-entropy criteria for average-case hardness
  (`Frontier.agreement_le_moment_sweeps`); conditional prefix potentials bound the
  square-root moment without assuming independent signals. Sumset bias also survives
  injective affine changes of input coordinates (`Frontier.FlatSumsetBias.affine_pullback`).
* A binary tree of regions has a weighted frontier bound with residual factor `(K - 1)^3`.
  Its network realization charges the **union** of the parent and two child boundaries,
  together with locally read inputs. It assumes all inputs are read and unique satisfying traces.
* Updating an independent set of cubic-graph vertices to median neighbour keys cannot
  increase any threshold cut. Local gains add exactly.

These refine the method without establishing a better universal `4.5625…` coefficient.
The [communication investigation](research/communication/README.md) records the exact
missing supply bound and a shared-selector circuit that defeats a marginal-entropy shortcut.
The [restriction investigation](research/communication/restrictions.md) derives adaptive
branch accounting, gives two paid local reductions, and checks an affine compression of a
low-fanout obstruction. It leaves the universal structural coverage theorem open.
The [additive continuation](research/communication/additive.md) proves threshold demand
for generators that emit overlapping vectors. Its affine-interface compiler retains every
code constraint in one syndrome state and can charge the exact trellis rank at each cut.
The abstract exact and coherent weighted demand theorems are checked in Lean; the compiler is a
paper proof with finite checks. Its `4.7812…` bound for cubic parity prefixes with arbitrary
nonlinear continuations is restricted to that architecture, not a universal improvement.
Joint encoding further avoids charging visible interface values separately from syndrome
information they already determine. The underlying subspace/rank identity is checked in
`Frontier.LinearBoundary.finrank_joint`; the compiler instantiation remains a paper proof
with finite checks, described in the [joint-code note](research/communication/joint.md).
Unique generation also gives an average-case version: the checked additive peeling
bound has remainder `(K-1)^2(D_0+D_1)/2^(n+1)`. The compiler's algebraic uniqueness
certificate is checked, while its full circuit instantiation remains a paper proof.
The new rank-profile module checks mixed-fiber cardinalities and transfers systematic
code pathwidth to a wide cut in every circuit layout with all inputs reachable.
A universal improvement still requires a capacity supply theorem or a uniform quantitative
Gaussian gain bound.
The paper presents the core method and the decomposable bound; the other refinements are
checked in Lean but not expounded there. [RESEARCH.md](RESEARCH.md) records them and the
remaining proof obligations.

The [OpenAI mathematics synthesis](research/openai-math/index.md) compares a pinned
download of `openai/math` with these techniques. It adds checked compatibility of
conditional upper potentials, source-specific transfer obligations, and finite
comparisons of transition capacity with restriction savings. It establishes no
new universal circuit coefficient.

## How the proof is factored

| Module | Content |
| --- | --- |
| `Frontier/Rectangle.lean` | Rectangle-free sets and the support lemma |
| `Frontier/Extractor.lean` | Sumset dispersers have rectangle-free fibers |
| `Frontier/Sweep.lean` | Abstract splicing messages and the frontier counting lemma |
| `Frontier/AdditiveSweep.lean`, `Frontier/AverageCase/Additive.lean` | Exact additive demand and coherent weighted peeling with flat-sumset bias |
| `Frontier/Decomposable.lean` | Smooth decomposable DAGs, certificate substitution, and threshold counting |
| `Frontier/Multigraph.lean` | Multigraphs, layouts, cycle rank, and the layout hypothesis |
| `Frontier/Network.lean` | Constraint networks, the separator lemma, and the frontier sweep along a layout, from which every sweep in the development is built |
| `Frontier/Compiler.lean` | Circuits of fan-in `r` with any outputs as exact networks of degree `r + 1` |
| `Frontier/Demand.lean` | Demand and supply: the comparison that ends every lower bound |
| `Frontier/Reduction.lean`, `Frontier/LowerBound.lean` | The main theorem |
| `Frontier/Layouts/*.lean`, `Frontier/Layouts.lean` | The layout bound: kernels, Sheppard's bound, concentration, median layouts, Gaussian scores, compression |
| `Frontier/Projection.lean`, `Frontier/Nondeterministic.lean` | Existential projection and the same lower bounds for verifiers |
| `Frontier/Signals.lean` | Frontier capacity measured by distinct signals |
| `Frontier/Boundary/*.lean` | Hypergraph cuts, exact linear syndrome states, transition codes |
| `Frontier/Boundary/Joint.lean` | Joint rank of visible observations and shared linear information |
| `Frontier/Boundary/Fiber.lean`, `Frontier/Boundary/Rank.lean`, `Frontier/Boundary/MDS.lean` | Mixed fibers, linear rank/pathwidth demand, and nonlinear MDS lower bounds |
| `Frontier/AverageCase/*.lean` | Coherent weighted peeling, circuit agreement bounds, and sumset bias |
| `Frontier/AverageCase/Pruning.lean` | Transition deletion with a weighted tail budget |
| `Frontier/AverageCase/Capacity.lean`, `Frontier/Boundary/Communication.lean` | Capped transition masses, square-root agreement bounds, and conditional prefix potentials |
| `Frontier/Tree.lean`, `Frontier/Tree/Network.lean` | Weighted tree frontiers and joint merge capacity |
| `Frontier/Layouts/General.lean`, `Frontier/Layouts/Local.lean` | Every fixed degree; independent local cut improvements |
| `Frontier/Layouts/VertexGaussian.lean` | Gaussian vertex scores and the per-edge crossing bound in every degree |
| `Frontier/Layouts/Support.lean`, `Frontier/Layouts/Multi*.lean`, `Frontier/Layouts/BoundedDegree.lean` | Multigraph compression, Gaussian concentration with multiplicities, and cycle-rank coefficients in every fixed degree, `2/5` at degree four |
| `Frontier/Main.lean` | Binary, ternary, and every fixed fan-in bounds for dense rectangle-free families |
| `Frontier/Linear/*.lean` | Totally regular maps, Cauchy matrices, linear capacity, linearization, arithmetic circuits |
| `Frontier/Arithmetic/*.lean` | Infinitesimal splicing, mixed-Hessian frontier rank, determinant demand and circuit lower bounds |
| `Frontier/Components.lean`, `Frontier/Ledger/*.lean` | Layouts of disconnected graphs; ledgers for gates of unbounded fan-in |
| `Frontier/ForMathlib`, `Frontier/ForCslib` | Upstreaming candidates |

## The paper

`paper/frontier.tex` is the accompanying exposition: the proof, the design decisions behind the
formal statements, the graph theory behind the layout coefficients, related work, and an index
from the paper to the Lean declarations. Build it with

```
./scripts/build-paper.sh
```

This writes `paper/frontier.pdf` with the source commit in its reproducibility paragraph.
Build from a clean checkout for an immutable snapshot; a dirty checkout is explicitly marked.
The generated PDF and `paper/revision.tex` are ignored by Git. A TeX installation with
`latexmk` is required.

## Building

The project depends on [CSLib](https://github.com/leanprover/cslib) (commit `89dc6fb`) and on
the Mathlib commit that CSLib pins (`9a6fbe0`), with toolchain `leanprover/lean4:v4.35.0-rc3`.
To bump, choose a CSLib commit first and copy its Mathlib `rev` and toolchain.

```
lake exe cache get
lake build --wfail
lake env lean scripts/Audit.lean
lake env lean -DwarningAsError=true examples/Compiler.lean
python3 scripts/check_algorithms.py
python3 scripts/check_communication.py
python3 research/communication/restrictions.py
python3 research/communication/syndrome_generator.py
python3 research/communication/unambiguous.py
python3 research/communication/rank_profiles.py
```

The audit checks the exact axiom lists of the principal results and fails if any list changes.
It also runs in CI. The paper's theorem-to-declaration index identifies the checked statements;
the audit does not verify the external extractor construction or the algorithmic claims.
For statement comparison and kernel replay, run the separate Docker-based gate:

```
python3 scripts/comparator.py self-test
python3 scripts/comparator.py check
```

It compares every public library theorem against a pinned source reference and checks all
theorem proofs, including unused private lemmas. See the [harness guide](verification/comparator/README.md)
for prerequisites, reports, isolation, and the deliberate reference-update procedure.

The Python script independently compares raw-edge, signal-state, and ledger counting with
exhaustive circuit evaluation, checks exact conditional moments against full enumeration,
and verifies rectangle peeling and threshold charges in an unambiguous program with guess
layers, including asymmetric thresholds, nonuniform weights, and shared error budgets.
It includes repeated arguments, constants, unused inputs, noncancellative monoids, and arbitrary
vertex orders. These finite checks exercise correctness; they do not prove the asymptotic
bounds or implement the full Gaussian layout construction.
The communication script checks capped costs on actual compiled traces, exhaustive codebook
choices, conditional moment identities, and the shared-selector counterexample. Its local
savings do not establish a universal improvement.
The restriction script checks local normalization against exhaustive truth tables,
fractional branch factors, and affine changes of basis. Its finite obstruction concerns
the implemented local rules, not minimum circuit size.
The syndrome-generator script compares generated supports with direct evaluation in the
global, pruned, and joint-code models, checks affine and graphic rank profiles, and detects
the false acceptances created by dropping the affine constraints. Joint-rank savings are
measured against an independent signal/syndrome bound, after removing repeated wire copies.

## License

Apache 2.0; see `LICENSE`.
