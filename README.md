# The Frontier Method

A self-contained, machine-checked account of circuit lower bounds from graph layouts.

**Theorem.** Assume that graphs of maximum degree `r + 1` have layouts whose frontiers carry at
most `(A + o(1)) β₁ + o(|V|)` edges, where `β₁` is the cycle rank. Let `S_n ⊆ U^n` be dense,
`K_n`-rectangle-free sets with `log K_n = o(n)`. Then every circuit with `s` inner gates of
fan-in at most `r` (gates of positive arity; constants are free), over *any* basis on the finite
alphabet `U`, deciding `S_n` satisfies

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
  (`Frontier.averageCase_sumset`). The explicit program partition and general distributional
  packing theorem remain paper proofs. The exponential remainder requires a fixed gap below `Ln`.
* **Nondeterministic circuits**: the same coefficient holds for verifier circuits, uniformly
  in the number of existential witness inputs (`Frontier.lowerBound_nondeterministic_gaussian`).
  The gate count includes every positive-arity verifier gate; the input count includes only
  ordinary inputs.
* **Signal capacity**: the proved frontier inequality can charge distinct circuit signals
  instead of their repeated edge copies (`Frontier.Compiler.ncard_accepted_le_signals`).
  This supplies a finer capacity theorem; improving the numerical coefficient still requires
  a stronger signal-layout bound.
* **Every fixed fan-in**: a spanning tree gives
  `cutwidth(G) ≤ β₁(G) + d floor(log₂ |V|)` in maximum degree `d`, hence `LayoutBound d 1`.
  Thus `(r - 1)s > (2 - ε)n` for every fixed fan-in `r ≥ 2`
  (`Frontier.layoutBound_one`, `Frontier.lowerBound_all_fanIn`). This is a general baseline;
  the Gaussian coefficient is stronger at fan-in two.
* **Linear maps and arithmetic circuits**: circuits computing a totally regular map `x ↦ M x`,
  over finite fields with any basis and over infinite fields with polynomial operations, need
  `(L - ε) N` gates; over every field of characteristic zero, arithmetic circuits computing the
  Cauchy map need `(L - ε) N` additions and multiplications (`Frontier.lowerBound_linear`,
  `Frontier.arith_cauchy_gaussian`). The displayed Cauchy matrices also work over prime fields
  of order `q ≥ 2N` (`Frontier.cauchyZMod_gaussian`).
* **Gates of unbounded fan-in**: the bound survives special gates with a *ledger* in a monoid `M`
  with `log |M| = o(n)`, for instance `o(n)` unbounded AND, OR, parity, or fixed-modulus count gates
  (`Frontier.lowerBound_ledger`, `Frontier.lowerBound_aggregate_gaussian`). The proof charges
  only the ordinary gates.

The exact and uniform average-case lower bounds, arithmetic instantiations, and layout theorem
are proved
with no `sorry`, using only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`),
in about 12,000 lines of Lean. The accompanying paper also gives a deterministic #SAT algorithm
for circuits of fan-in two with `s` positive-arity gates, running for every fixed `η > 0` in
time and space `O*(2^((1/L + η) s))`, where `1/L = 0.2191781936...`. Here `O*` suppresses
polynomial factors in the full circuit encoding and the number of inputs. With `m` inputs
reachable from the output, the sharper time bound is
`O*(2^(min(m, A(s-m)) + ηs))`. With a finite, efficiently evaluable ledger, the algorithm takes
`|M|^O(1) O*(2^((1/L + η) s_ord))`; this allows `k` unbounded AND/OR/parity/fixed-modulus gates
at an additional `O(k)` cost in the exponent.

The deterministic cubic-layout construction uses fixed-accuracy discretization and conditional
expectations, taking `f(ξ) h^3 polylog(h)` time on an `h`-vertex cubic graph; the polynomial degree
is independent of accuracy. The paper also proves exact counting with signal states and gives
a tree-limit calculation showing that the current local Gaussian straddling estimate is sharp.
The algorithms and their complexity bounds, this limiting calculation, the random-set existence
argument, the explicit program partition and general distributional packing bounds, and the
branching-program discussion are not formalized.

The new boundary results are checked in Lean as well:

* Signal cuts are exactly cuts of a signal hypergraph and have submodular cardinality.
  Transition encodings can replace wire counts; for linear constraints, feasible syndromes
  form `im L ∩ im R`, with the exact matroid-connectivity dimension.
* Pruning a coherent sweep to selected transitions preserves splicing. Discarded uniform
  probability mass `δ` contributes at most `δ/2` to the agreement bound.
* A binary tree of regions has a weighted frontier bound with residual factor `(K - 1)^3`.
  Its network realization charges the **union** of the parent and two child boundaries,
  together with locally read inputs. It assumes all inputs are read and unique satisfying traces.
* Updating an independent set of cubic-graph vertices to median neighbour keys cannot
  increase any threshold cut. Local gains add exactly.

These refine the method without establishing a better universal `4.5625…` coefficient.
That still requires a capacity supply theorem or a uniform quantitative Gaussian gain bound.
The paper gives complete proofs and credits the coding, communication-complexity, and
tensor-network precedents; [RESEARCH.md](RESEARCH.md) records the remaining proof obligations.

## How the proof is factored

| Module | Content |
| --- | --- |
| `Frontier/Rectangle.lean` | Rectangle-free sets and the support lemma |
| `Frontier/Extractor.lean` | Sumset dispersers have rectangle-free fibers |
| `Frontier/Sweep.lean` | Abstract splicing messages and the frontier counting lemma |
| `Frontier/Multigraph.lean` | Multigraphs, layouts, cycle rank, and the layout hypothesis |
| `Frontier/Network.lean` | Constraint networks, the separator lemma, and the frontier sweep along a layout, from which every sweep in the development is built |
| `Frontier/Compiler.lean` | Circuits of fan-in `r` with any outputs as exact networks of degree `r + 1` |
| `Frontier/Demand.lean` | Demand and supply: the comparison that ends every lower bound |
| `Frontier/Reduction.lean`, `Frontier/LowerBound.lean` | The main theorem |
| `Frontier/Layouts/*.lean`, `Frontier/Layouts.lean` | The layout bound: kernels, Sheppard's bound, concentration, median layouts, Gaussian scores, compression |
| `Frontier/Projection.lean`, `Frontier/Nondeterministic.lean` | Existential projection and the same lower bounds for verifiers |
| `Frontier/Signals.lean` | Frontier capacity measured by distinct signals |
| `Frontier/Boundary/*.lean` | Hypergraph cuts, exact linear syndrome states, transition codes |
| `Frontier/AverageCase/*.lean` | Coherent weighted peeling, circuit agreement bounds, and sumset bias |
| `Frontier/AverageCase/Pruning.lean` | Transition deletion with a weighted tail budget |
| `Frontier/Tree.lean`, `Frontier/Tree/Network.lean` | Weighted tree frontiers and joint merge capacity |
| `Frontier/Layouts/General.lean`, `Frontier/Layouts/Local.lean` | Every fixed degree; independent local cut improvements |
| `Frontier/Main.lean` | The `(L - ε) n` and `(4 - ε) n` bounds for dense rectangle-free families |
| `Frontier/Linear/*.lean` | Totally regular maps, Cauchy matrices, linear capacity, linearization, arithmetic circuits |
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
python3 scripts/check_algorithms.py
```

The audit checks the exact axiom lists of twenty-five principal results and fails if any list changes.
It also runs in CI. The paper's theorem-to-declaration index identifies the checked statements;
the audit does not verify the external extractor construction or the algorithmic claims.
The Python script independently compares raw-edge, signal-state, and ledger counting with
exhaustive circuit evaluation, checks exact conditional moments against full enumeration,
and verifies rectangle peeling and threshold charges in an unambiguous program with guess
layers, including asymmetric thresholds, nonuniform weights, and shared error budgets.
It includes repeated arguments, constants, unused inputs, noncancellative monoids, and arbitrary
vertex orders. These finite checks exercise correctness; they do not prove the asymptotic
bounds or implement the full Gaussian layout construction.

## License

Apache 2.0; see `LICENSE`.
