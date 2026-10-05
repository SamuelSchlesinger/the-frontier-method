/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Reduction
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The lower bound

**Main theorem** (`Frontier.lowerBound`). Fix a fan-in bound `r ≥ 2`, and suppose that graphs
of maximum degree `r + 1` have layouts of width `(A + o(1)) β₁ + o(|V|)` (`LayoutBound (r + 1) A`).
Let `S_n ⊆ U^n` be `K_n`-rectangle-free sets over a finite alphabet `U`, with `log K_n = o(n)`
and `|S_n| ≥ |U| ^ (n - o(n))`. Then for every `ε > 0` and all large `n`, every circuit deciding
`S_n` over any basis of fan-in at most `r` on `U` has size `s` with

`(r - 1) s > (1 + 1/A - ε) n`.

For fan-in two (`Frontier.lowerBound_fanInTwo`) the graphs are subcubic and the bound reads
`s > (1 + 1/A - ε) n`.

The proof is the reduction theorem followed by arithmetic. A circuit of size `s` gives a graph
of cycle rank about `(r - 1) s - n`, all of whose layouts have width about `n`. The layout
hypothesis provides a layout of width about `A ((r - 1) s - n)`. So `n ≤ A ((r - 1) s - n) + o(n)`,
that is, `(r - 1) s ≥ (1 + 1/A - o(1)) n`.

The fixed-length form `Frontier.logb_ncard_le_of_layout` keeps every lower-order term explicit.

## Instances

For fan-in two:

* with `A = 1/3`, from the cubic pathwidth bound `h/6` of Fomin and Høie, the coefficient is
  `4`;
* with `A = (3/π) arccos((1 + 2√2)/4) ≈ 0.2807`, from Gaussian edge-score layouts, the
  coefficient is `1 + π/(3 arccos((1 + 2√2)/4)) ≈ 4.5625`.

Neither layout theorem is formalized here; both enter through `LayoutBound`.
-/

@[expose] public section

namespace Frontier

open Cslib.Circuits Set Filter Asymptotics

universe u v

section FixedLength

variable {U : Type u} [Finite U] [Nontrivial U] {σ : Signature.{v}} {n : ℕ}
  {I : Interpretation σ U} {Acc : Set U} {c : Circuit σ n 1} {S : Set (Fin n → U)} {K r : ℕ}

/-- **The lower bound at a fixed length.** Let `r ≥ 2`. If every connected, loopless
multigraph of maximum degree `r + 1` has a layout of width at most `a β₁ + b |V| + C`, then a
circuit of size `s` with fan-in at most `r` deciding a `K`-rectangle-free set `S ⊆ U^n` with
`|S| ≥ q K^2` satisfies, writing `s' = (r - 1) s`,

`log_q |S| ≤ a (s' - n + log_q K + 1) + b (n + 3s' + 2) + C + (r + 2) + 3 log_q K +`
`log_q (n + 3s' + 3)`.
-/
theorem logb_ncard_le_of_layout {a b C : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 2 ≤ r)
    (hlayout : ∀ (V E : Type) [Finite V] [Finite E] (G : Multigraph V E),
      G.Connected → G.Loopless → G.MaxDegreeLE (r + 1) →
        ∃ π : Layout V, ∀ t,
          ((G.cut (π.initial t)).ncard : ℝ) ≤ a * G.cycleRank + b * Nat.card V + C)
    (hfan : c.FanInAtMost r) (hS : Decides c I Acc S) (hfree : RectangleFree S K)
    (hbig : Nat.card U * K ^ 2 ≤ S.ncard) :
    Real.logb (Nat.card U) S.ncard ≤
      a * (((r - 1) * c.size : ℕ) - n + Real.logb (Nat.card U) K + 1) +
        b * (n + 3 * ((r - 1) * c.size : ℕ) + 2) + C + (r + 2) +
        3 * Real.logb (Nat.card U) K +
        Real.logb (Nat.card U) (n + 3 * ((r - 1) * c.size : ℕ) + 3) := by
  obtain ⟨V, E, _, _, G, hconn, hloop, hdeg, hV, hrank, hwidth⟩ :=
    exists_graph_of_decides hr hfan hS hfree hbig
  obtain ⟨π, hπ⟩ := hlayout V E G hconn hloop hdeg
  set B := a * G.cycleRank + b * Nat.card V + C
  have hB : 0 ≤ B := by simpa [Layout.initial_zero] using hπ 0
  -- `(r + 1) s ≤ 3 (r - 1) s` because `r ≥ 2`.
  have hV' : Nat.card V ≤ n + 3 * ((r - 1) * c.size) + 2 := by
    have : (r + 1) * c.size ≤ 3 * ((r - 1) * c.size) := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  have hVR : (Nat.card V : ℝ) ≤ n + 3 * ((r - 1) * c.size : ℕ) + 2 := by exact_mod_cast hV'
  have hq : (1 : ℝ) < Nat.card U := by exact_mod_cast Finite.one_lt_card
  have hlogV : Real.logb (Nat.card U) (Nat.card V + 1) ≤
      Real.logb (Nat.card U) (n + 3 * ((r - 1) * c.size : ℕ) + 3) :=
    Real.logb_le_logb_of_le hq (by positivity) (by linarith)
  have hwidth := hwidth π ⌊B⌋₊ fun t => Nat.le_floor (hπ t)
  have hfloor : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le hB
  have hrankB : a * G.cycleRank ≤
      a * (((r - 1) * c.size : ℕ) - n + Real.logb (Nat.card U) K + 1) :=
    mul_le_mul_of_nonneg_left hrank ha
  have hVB : b * Nat.card V ≤ b * (n + 3 * ((r - 1) * c.size : ℕ) + 2) :=
    mul_le_mul_of_nonneg_left hVR hb
  linarith

end FixedLength

/-! ### Asymptotics -/

/-- `log (α n + β) = o(n)` for constants `α ≥ 0` and `β ≥ 1`. -/
theorem isLittleO_log_affine {α β : ℝ} (hα : 0 ≤ α) (hβ : 1 ≤ β) :
    (fun n : ℕ => Real.log (α * n + β)) =o[atTop] fun n => (n : ℝ) := by
  have hlog : (fun n : ℕ => Real.log n) =o[atTop] fun n => (n : ℝ) :=
    Real.isLittleO_log_id_atTop.comp_tendsto tendsto_natCast_atTop_atTop
  refine IsLittleO.of_bound fun δ hδ => ?_
  filter_upwards [hlog.bound (show 0 < δ / 2 by positivity), eventually_ge_atTop 1,
    eventually_ge_atTop ⌈2 * Real.log (α + β) / δ⌉₊] with n hn hn1 hnC
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnC' : 2 * Real.log (α + β) / δ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hnC)
  simp only [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)] at hn ⊢
  rw [abs_of_nonneg (Real.log_nonneg (by nlinarith))]
  -- `log (α n + β) ≤ log ((α + β) n) = log (α + β) + log n`.
  have hle : Real.log (α * n + β) ≤ Real.log (α + β) + Real.log n := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hlogn : Real.log n ≤ δ / 2 * n := (le_abs_self _).trans hn
  have hC : Real.log (α + β) ≤ δ / 2 * n := by
    have := (div_le_iff₀ hδ).mp hnC'
    linarith
  linarith

section Main

variable {U : Type u} [Finite U] [Nontrivial U]

/-- The main theorem, for `A ε ≤ 1`. -/
private theorem lowerBound_aux {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A)
    (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) (hεA : A * ε ≤ 1) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → Decides c I Acc (S n) →
        (1 + 1 / A - ε) * n < ((r - 1) * c.size : ℕ) := by
  set q := Nat.card U
  set L := Real.log q
  have hq : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  have hL : 0 < L := Real.log_pos hq
  -- Spend the layout slack so that `η (4 + 4/A) = A ε / 2`.
  set η := A * ε / (2 * (4 + 4 / A)) with hη_def
  have hη : 0 < η := by positivity
  have hηε : η * (4 + 4 / A) = A * ε / 2 := by
    rw [hη_def]; field_simp
  obtain ⟨C, hC⟩ := hlayout η hη
  -- The error budget: each lower-order term is eventually at most `δ n`.
  set δ := A * ε * L / 10 with hδ_def
  have hδ : 0 < δ := by positivity
  have hδL : δ ≤ L / 10 := by
    rw [hδ_def]; have := mul_le_mul_of_nonneg_right hεA hL.le; linarith
  set κ := A + η + 3
  have hκ : 3 ≤ κ := by linarith
  have hlogV := isLittleO_log_affine (α := 4 + 3 / A) (β := 3) (by positivity) (by norm_num)
  filter_upwards [hfree, hK.bound (show 0 < δ / κ by positivity), hdense.bound hδ,
    hlogV.bound hδ, eventually_ge_atTop 2,
    eventually_ge_atTop ⌈|(A + 3 * η + C + r + 2) * L| / δ⌉₊] with n hfree hKn hdn hlogn hn2 hnC
  intro σ I Acc c hfan hS
  by_contra! hs
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hK1 := hfree.pos
  have hKR : (1 : ℝ) ≤ K n := by exact_mod_cast hK1
  have hlogK : 0 ≤ Real.log (K n) := Real.log_nonneg hKR
  simp only [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ n),
    abs_of_nonneg hlogK] at hKn hdn hlogn
  have hKn' : κ * Real.log (K n) ≤ δ * n := by
    have := mul_le_mul_of_nonneg_left hKn (by linarith : (0 : ℝ) ≤ κ)
    rwa [← mul_assoc, mul_div_cancel₀ _ (by linarith : κ ≠ 0)] at this
  have hdn' : n * L - δ * n ≤ Real.log (S n).ncard := by linarith [le_abs_self (n * L -
    Real.log (S n).ncard)]
  -- The set is large enough for the reduction: `q K^2 ≤ |S|`.
  have hSpos : 0 < Real.log (S n).ncard := by nlinarith
  have hSpos' : (0 : ℝ) < (S n).ncard := by
    by_contra! h
    have : ((S n).ncard : ℝ) = 0 := le_antisymm h (Nat.cast_nonneg _)
    rw [this, Real.log_zero] at hSpos
    exact lt_irrefl _ hSpos
  have hbig : q * K n ^ 2 ≤ (S n).ncard := by
    have hlog : Real.log (q * K n ^ 2 : ℝ) ≤ Real.log (S n).ncard := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      push_cast
      have : δ / κ * n ≤ δ * n := by
        gcongr; exact div_le_self hδ.le (by linarith)
      have : δ * n ≤ L / 10 * n := by gcongr
      have : 2 * L ≤ n * L := by nlinarith
      linarith
    exact_mod_cast (Real.log_le_log_iff (by positivity) hSpos').mp hlog
  -- The bound at length `n`, with logarithms to base `e`.
  have key := logb_ncard_le_of_layout (by positivity : 0 ≤ A + η) hη.le hr hC hfan hS hfree hbig
  simp only [Real.logb] at key
  set s : ℝ := (((r - 1) * c.size : ℕ) : ℝ)
  set lS := Real.log (S n).ncard
  set lK := Real.log (K n)
  set lV := Real.log (n + 3 * s + 3)
  have key' : lS ≤ (A + η) * (L * (s - n)) + κ * lK +
      ((A + η) * L + 2 * η * L + C * L + (r + 2) * L) + η * L * (n + 3 * s) + lV := by
    have h := (div_le_iff₀ hL).mp key
    have : ((A + η) * (s - n + lK / L + 1) + η * (n + 3 * s + 2) + C + (r + 2) + 3 * (lK / L) +
        lV / L) * L = (A + η) * (L * (s - n)) + κ * lK +
          ((A + η) * L + 2 * η * L + C * L + (r + 2) * L) + η * L * (n + 3 * s) + lV := by
      field_simp; ring
    linarith
  -- Bound the terms that grow with `s`.
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hsA : s ≤ (1 + 1 / A) * n := by nlinarith
  have h1 : (A + η) * (L * (s - n)) ≤ (1 - A * ε + η / A) * (n * L) := by
    have hsn : L * (s - n) ≤ L * ((1 / A - ε) * n) := by
      gcongr; linarith
    calc (A + η) * (L * (s - n)) ≤ (A + η) * (L * ((1 / A - ε) * n)) := by gcongr
      _ = (1 - A * ε + η / A) * (n * L) - η * ε * (n * L) := by field_simp; ring
      _ ≤ (1 - A * ε + η / A) * (n * L) := by
          have : 0 ≤ η * ε * (n * L) := by positivity
          linarith
  have h2 : η * L * (n + 3 * s) ≤ η * (4 + 3 / A) * (n * L) := by
    calc η * L * (n + 3 * s) ≤ η * L * (n + 3 * ((1 + 1 / A) * n)) := by gcongr
      _ = η * (4 + 3 / A) * (n * L) := by ring
  have h3 : lV ≤ δ * n := by
    have h3s := mul_le_mul_of_nonneg_left hsA (by norm_num : (0 : ℝ) ≤ 3)
    have : (4 + 3 / A) * n = n + 3 * ((1 + 1 / A) * n) := by ring
    have : lV ≤ Real.log ((4 + 3 / A) * n + 3) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith [le_abs_self (Real.log ((4 + 3 / A) * n + 3))]
  have h4 : (A + η) * L + 2 * η * L + C * L + (r + 2) * L ≤ δ * n := by
    have hnC' : |(A + 3 * η + C + r + 2) * L| / δ ≤ n :=
      (Nat.le_ceil _).trans (by exact_mod_cast hnC)
    have := (div_le_iff₀ hδ).mp hnC'
    have : (A + η) * L + 2 * η * L + C * L + (r + 2) * L = (A + 3 * η + C + r + 2) * L := by
      ring
    linarith [le_abs_self ((A + 3 * η + C + r + 2) * L)]
  -- Combine: `(A ε / 2) n L ≤ 4 δ n = (2/5) A ε n L`, which is false.
  have hsum : (1 - A * ε + η / A) * (n * L) + η * (4 + 3 / A) * (n * L) =
      (1 - A * ε / 2) * (n * L) := by
    have : η / A + η * (4 + 3 / A) = η * (4 + 4 / A) := by ring
    linear_combination (n * L) * (this.trans hηε)
  have hfinal : A * ε / 2 * (n * L) ≤ 4 * δ * n := by linarith
  have : 4 * δ * n = 2 / 5 * (A * ε) * (n * L) := by rw [hδ_def]; ring
  have hpos : 0 < A * ε * (n * L) := by positivity
  linarith

/-- **The frontier lower bound.** Let `r ≥ 2` and assume the layout hypothesis for maximum
degree `r + 1` with coefficient `A > 0`. Let `S_n ⊆ U^n` be `K_n`-rectangle-free sets over a
finite alphabet `U` with at least two symbols, with `log K_n = o(n)` and
`n log |U| - log |S_n| = o(n)`. Then for every `ε > 0`, for all large `n`, every circuit of size
`s` with fan-in at most `r` deciding `S_n`, over any basis and interpretation on `U`, has
`(r - 1) s > (1 + 1/A - ε) n`. -/
theorem lowerBound {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound (r + 1) A)
    (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → Decides c I Acc (S n) →
        (1 + 1 / A - ε) * n < (r - 1) * c.size := by
  -- A smaller `ε` gives a stronger statement, so assume `A ε ≤ 1`.
  set ε' := min ε (1 / A)
  have hε' : 0 < ε' := lt_min hε (by positivity)
  have hε'A : A * ε' ≤ 1 := by
    have := mul_le_mul_of_nonneg_left (min_le_right ε (1 / A)) hA.le
    rwa [mul_one_div_cancel hA.ne'] at this
  filter_upwards [lowerBound_aux hr hA hlayout S K hfree hK hdense hε' hε'A] with n hn
  intro σ I Acc c hfan hS
  have h := hn σ I Acc c hfan hS
  rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one] at h
  refine lt_of_le_of_lt ?_ h
  gcongr
  exact min_le_left _ _

/-- **The frontier lower bound for fan-in two.** Assume the layout hypothesis for subcubic graphs
with coefficient `A > 0`. Under the hypotheses of `Frontier.lowerBound`, for every `ε > 0` and all
large `n`, every circuit with fan-in at most two deciding `S_n`, over any basis and
interpretation on `U`, has more than `(1 + 1/A - ε) n` gates. -/
theorem lowerBound_fanInTwo {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound 3 A)
    (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → Decides c I Acc (S n) →
        (1 + 1 / A - ε) * n < c.size := by
  filter_upwards [lowerBound le_rfl hA hlayout S K hfree hK hdense hε] with n hn
  intro σ I Acc c hfan hS
  have h := hn σ I Acc c hfan hS
  norm_num at h ⊢
  exact h

end Main

end Frontier
