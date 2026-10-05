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
  balanced sumset dispersers, such as extractors for the sum of two sources
  (`Frontier.lowerBound_sumsetDisperser`).
* **Linear maps and arithmetic circuits**: circuits computing a totally regular map `x ↦ M x`,
  over finite fields with any basis and over infinite fields with polynomial operations, need
  `(L - ε) N` gates; over every field of characteristic zero, arithmetic circuits computing the
  Cauchy map need `(L - ε) N` additions and multiplications (`Frontier.lowerBound_linear`,
  `Frontier.arith_cauchy_gaussian`, `Frontier.cauchyZMod_gaussian`).
* **Gates of unbounded fan-in**: the bound survives special gates with a *ledger* in a monoid `M`
  with `log |M| = o(n)`, for instance `o(n)` unbounded AND, OR, parity, or modular-count gates
  (`Frontier.lowerBound_ledger`, `Frontier.lowerBound_aggregate_gaussian`). The proof charges
  only the ordinary gates.

Everything is proved, with no `sorry`, using only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`), in about 8,600 lines of Lean. The accompanying
paper also gives a #SAT algorithm for circuits of fan-in two with `s` gates, based on the same
frontiers, running for every `η > 0` in time `2^((1/4 + η) s)` deterministically and in expected
time `2^((0.2192 + η) s)` with randomness. Its correctness rests on the formalized compiler and
layout theorems, but the algorithm and its running time are not formalized.

## How the proof is factored

| Module | Content |
| --- | --- |
| `Frontier/Rectangle.lean` | Rectangle-free sets and the support lemma |
| `Frontier/Extractor.lean` | Sumset dispersers have rectangle-free fibers |
| `Frontier/Sweep.lean` | Sweeps (abstract read-once protocols) and the frontier counting lemma |
| `Frontier/Multigraph.lean` | Multigraphs, layouts, cycle rank, and the layout hypothesis |
| `Frontier/Network.lean` | Constraint networks, the separator lemma, and the frontier sweep along a layout, from which every sweep in the development is built |
| `Frontier/Compiler.lean` | Circuits of fan-in `r` with any outputs as exact networks of degree `r + 1` |
| `Frontier/Demand.lean` | Demand and supply: the comparison that ends every lower bound |
| `Frontier/Reduction.lean`, `Frontier/LowerBound.lean` | The main theorem |
| `Frontier/Layouts/*.lean`, `Frontier/Layouts.lean` | The layout bound: kernels, Sheppard's bound, concentration, median layouts, Gaussian scores, compression |
| `Frontier/Main.lean` | The unconditional `(L - ε) n` and `(4 - ε) n` bounds |
| `Frontier/Linear/*.lean` | Totally regular maps, Cauchy matrices, linear capacity, linearization, arithmetic circuits |
| `Frontier/Components.lean`, `Frontier/Ledger/*.lean` | Layouts of disconnected graphs; ledgers for gates of unbounded fan-in |
| `Frontier/ForMathlib`, `Frontier/ForCslib` | Upstreaming candidates |

## The paper

`paper/frontier.tex` is the accompanying exposition: the proof, the design decisions behind the
formal statements, the graph theory behind the layout coefficients, related work, and an index
from the paper to the Lean declarations. Build it with

```
cd paper && latexmk -pdf frontier.tex
```

## Building

The project depends on [CSLib](https://github.com/leanprover/cslib) (commit `89dc6fb`) and on
the Mathlib commit that CSLib pins (`9a6fbe0`), with toolchain `leanprover/lean4:v4.35.0-rc3`.
To bump, choose a CSLib commit first and copy its Mathlib `rev` and toolchain.

```
lake exe cache get
lake build
```

## License

Apache 2.0; see `LICENSE`.
