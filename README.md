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

The general lower-bound theorems, arithmetic instantiations, and layout theorem are proved
with no `sorry`, using only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`),
in about 8,600 lines of Lean. The accompanying paper also gives a deterministic #SAT algorithm
for circuits of fan-in two with `s` positive-arity gates, running for every fixed `η > 0` in
time and space `O*(2^((1/L + η) s))`, where `1/L = 0.2191781936...`. Here `O*` suppresses
polynomial factors in the full circuit encoding and the number of inputs; its polynomial
degree may depend on `η`. The proof enumerates boundedly independent, finite-precision
Gaussian samples to find a layout. The algorithms, their complexity bounds, this
derandomization, the random-set existence argument, and the branching-program discussion
are not formalized.

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
```

The audit checks the exact axiom lists of eight principal results and fails if any list changes.
It also runs in CI. The paper's theorem-to-declaration index identifies the checked statements;
the audit does not verify the external extractor construction or the algorithmic claims.

## License

Apache 2.0; see `LICENSE`.
