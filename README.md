# The Frontier Method

A self-contained, machine-checked account of a circuit lower bound from graph layouts.

**Theorem.** Assume that graphs of maximum degree `r + 1` have layouts whose frontiers carry at
most `(A + o(1)) β₁ + o(|V|)` edges, where `β₁` is the cycle rank. Let `S_n ⊆ U^n` be dense,
`K_n`-rectangle-free sets with `log K_n = o(n)`. Then every circuit of size `s` and fan-in at
most `r`, over *any* basis on the finite alphabet `U`, deciding `S_n` satisfies

```
(r - 1) s > (1 + 1/A - ε) n        for all large n.
```

For fan-in two this is `s > (L - ε) n` with `L = 1 + 1/A`: the known layout coefficients
`A = 1/3` and `A ≈ 0.2807` give `(4 - ε) n` and `(4.5625 - ε) n`.

In Lean (`Frontier/LowerBound.lean`):

```lean
theorem lowerBound {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound (r + 1) A)
    (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → Decides c I Acc (S n) →
        (1 + 1 / A - ε) * n < (r - 1) * c.size
```

The layout bound is the single graph-theoretic input, stated as the hypothesis
`Frontier.LayoutBound` so that any layout theorem can be plugged in. It is proved for subcubic
graphs with `A = (3/π) arccos((1 + 2√2)/4)` by Gaussian edge scores (`Frontier.layoutBound_gaussian`),
which gives the unconditional theorems (`Frontier/Main.lean`):

```lean
theorem lowerBound_gaussian ... :
    ∀ᶠ n in atTop, ∀ σ I Acc (c : Circuit σ n 1), c.FanInAtMost 2 → Decides c I Acc (S n) →
      (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n < c.size
theorem lowerBound_four ... : ... (4 - ε) * n < c.size
```

Everything is proved, with no `sorry`, using only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

## How the proof is factored

| Module | Content |
| --- | --- |
| `Frontier/Rectangle.lean` | Rectangle-free sets and the support lemma |
| `Frontier/Sweep.lean` | Sweeps (abstract read-once protocols) and the frontier counting lemma |
| `Frontier/Multigraph.lean` | Multigraphs, layouts, cycle rank, and the layout hypothesis |
| `Frontier/Network.lean` | Constraint networks, the separator lemma, and sweeping along a layout |
| `Frontier/Compiler.lean` | Circuits of fan-in `r` as exact networks of degree `r + 1` |
| `Frontier/Reduction.lean` | Small circuit ⇒ graph of small cycle rank with only wide layouts |
| `Frontier/LowerBound.lean` | The main theorem |
| `Frontier/Layouts/*.lean`, `Frontier/Layouts.lean` | The layout bound: kernels, Sheppard's bound, concentration, median layouts, Gaussian scores, compression |
| `Frontier/Main.lean` | The unconditional `(L - ε) n` and `(4 - ε) n` bounds |
| `Frontier/ForMathlib`, `Frontier/ForCslib` | Upstreaming candidates |

## The paper

`paper/frontier.tex` is the accompanying exposition: the proof, the design decisions behind the
formal statements, the graph theory behind the layout coefficients, and an index from the paper
to the Lean declarations. Build it with

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
