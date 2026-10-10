/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Parity.Reduction

/-!
# The explicit redundancy loss in the circuit lower bound

With layout coefficient `0 < A ≤ 1`, free supplied linear inputs give
`(1 + 1/A - ε) n < size + (1/A - 1) * readRedundancy`.
The number of supplied inputs and their linear map are arbitrary, and correctness
is required only on their image. Sublinear read redundancy preserves the leading
coefficient. The theorem retains a loss for linear redundancy; eliminating it is
the remaining full-preservation problem.
-/

@[expose] public section

namespace Frontier

open Set Filter Asymptotics Cslib.Circuits

universe u v

/-- Numerical demand and supply with the consistency cost retained. -/
theorem lowerBound_of_graph_with_redundancy {U : Type u} [Finite U] [Nontrivial U]
    {A : ℝ} (hA : 0 < A) (hA1 : A ≤ 1) (hlayout : LayoutBound 3 A)
    (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (gates b : ℕ) (V E : Type) [Finite V] [Finite E] (G : Multigraph V E),
      G.Connected → G.Loopless → G.MaxDegreeLE 3 →
      Nat.card V ≤ 4 * gates + 3 →
      (G.cycleRank : ℝ) + b ≤ gates - n + Real.logb (Nat.card U) (K n) + 1 →
      (∀ (π : Layout V) (w : ℕ), (∀ t, (G.cut (π.initial t)).ncard ≤ w) →
        Real.logb (Nat.card U) (S n).ncard ≤
          w + 4 + b + 3 * Real.logb (Nat.card U) (K n) +
            Real.logb (Nat.card U) (Nat.card V + 1)) →
      (1 + 1 / A - ε) * n < gates + (1 / A - 1) * b := by
  set q := Nat.card U
  have hq : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  have hL : 0 < Real.log q := Real.log_pos hq
  have hL2 : Real.log 2 ≤ Real.log q :=
    Real.log_le_log two_pos (by exact_mod_cast Finite.one_lt_card)
  have hcoef : 0 ≤ 1 / A - 1 := sub_nonneg.mpr ((le_div_iff₀ hA).mpr (by simpa using hA1))
  set e : ℕ → ℝ := fun n => (n - Real.logb q (S n).ncard) + 4 * Real.logb q (K n) + 5
  have he : e =o[atTop] fun n => (n : ℝ) := by
    have h1 := isLittleO_sub_logb_ncard S hdense
    have h2 : (fun n : ℕ => 4 * Real.logb q (K n)) =o[atTop] fun n => (n : ℝ) :=
      (hK.const_mul_left (4 / Real.log q)).congr_left fun n => by
        simp only [Real.logb]; ring
    have h3 : (fun _ : ℕ => (5 : ℝ)) =o[atTop] fun n => (n : ℝ) :=
      isLittleO_const_left.mpr (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop))
    exact (h1.add h2).add h3
  set κ : ℝ := 4 + 1 / Real.log 2
  have hκ : 0 ≤ κ := by positivity
  obtain ⟨η, hη, H⟩ := eventually_lt_of_demand hA hκ hε
  obtain ⟨C, hC⟩ := hlayout η hη
  have hbig := eventually_card_mul_sq_le_ncard S K hfree hK hdense
  filter_upwards [H η hη le_rfl C e he, hfree, hbig] with n hn hfreen hbign
  intro gates b V E _ _ G hconn hloop hdeg hV hrank hwidth
  obtain ⟨π, hπ⟩ := hC V E G hconn hloop hdeg
  set B := (A + η) * G.cycleRank + η * Nat.card V + C
  have hB : 0 ≤ B := by simpa [Layout.initial_zero] using hπ 0
  have hwidth := hwidth π ⌊B⌋₊ fun t => Nat.le_floor (hπ t)
  set s : ℝ := gates + (1 / A - 1) * b
  have hgs : (gates : ℝ) ≤ s := le_add_of_nonneg_right (mul_nonneg hcoef (Nat.cast_nonneg b))
  have hs : 0 ≤ s := (Nat.cast_nonneg gates).trans hgs
  have hK1 : (1 : ℝ) ≤ K n := by exact_mod_cast hfreen.pos
  have hlogK : 0 ≤ Real.logb q (K n) := Real.logb_nonneg hq hK1
  have hSne : (S n).Nonempty := by
    rw [← ncard_pos (toFinite _)]
    exact lt_of_lt_of_le (Nat.mul_pos Nat.card_pos (pow_pos hfreen.pos 2)) hbign
  have hlogS := logb_ncard_le_self (S n) hSne
  have hlogV : Real.logb q (Nat.card V + 1) ≤ κ * Real.log (Nat.card V + 1) := by
    have h0 : 0 ≤ Real.log (Nat.card V + 1) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (Nat.card V)])
    have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    calc Real.logb q (Nat.card V + 1) ≤ Real.log (Nat.card V + 1) / Real.log 2 :=
          div_le_div_of_nonneg_left h0 h2 hL2
      _ ≤ κ * Real.log (Nat.card V + 1) := by
          rw [div_eq_mul_one_div, mul_comm]
          exact mul_le_mul_of_nonneg_right (by simp [κ]) h0
  have hVs : (Nat.card V : ℝ) ≤ κ * (n + s + 1) := by
    have h4 : (Nat.card V : ℝ) ≤ 4 * gates + 3 := by exact_mod_cast hV
    have hκ4 : 4 ≤ κ := by simp only [κ]; linarith [show 0 ≤ 1 / Real.log 2 by positivity]
    have hns : 0 ≤ (n : ℝ) + s + 1 := by positivity
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  apply hn s (Nat.card V) ((⌊B⌋₊ : ℝ) + b) hs (Nat.cast_nonneg _) hVs
  · dsimp [e]
    linarith
  · have hfloor : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le hB
    have hrank' : (G.cycleRank : ℝ) ≤ gates - n - b + e n := by
      dsimp [e]
      linarith
    have hmul := mul_le_mul_of_nonneg_left hrank' (by positivity : 0 ≤ A + η)
    have hid : (A + η) * (s - n + e n) -
        ((A + η) * (gates - n - b + e n) + b) = (η / A) * b := by
      dsimp [s]
      field_simp
      ring
    have hnonneg : 0 ≤ (η / A) * (b : ℝ) := by positivity
    linarith

/-- The unrestricted binary-circuit bound with arbitrary free linear inputs.
Only redundancy among reached forms is charged, with coefficient `1/A - 1`. -/
theorem lowerBound_linear_inputs {F : Type u} [Field F] [Finite F]
    {A : ℝ} (hA : 0 < A) (hA1 : A ≤ 1) (hlayout : LayoutBound 3 A)
    (S : ∀ n, Set (Fin n → F)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, SumsetFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card F) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (m : ℕ) (σ : Signature.{v}) (I : Interpretation σ F) (Acc : Set F)
      (c : Circuit σ m 1) (L : (Fin n → F) →ₗ[F] (Fin m → F)), c.FanInAtMost 2 →
      (∀ x, c.eval I (L x) 0 ∈ Acc ↔ x ∈ S n) →
        (1 + 1 / A - ε) * n < c.innerSize +
          (1 / A - 1) * (constraintNetwork I Acc c).readRedundancy L := by
  have hrect := hfree.mono fun _ h => h.rectangleFree
  filter_upwards [lowerBound_of_graph_with_redundancy hA hA1 hlayout S K hrect hK hdense hε,
    hfree, eventually_card_mul_sq_le_ncard S K hrect hK hdense] with n hn hf hb
  intro m σ I Acc c L hfan hc
  have hbig : K n ^ 2 ≤ (S n).ncard :=
    (Nat.le_mul_of_pos_left _ Nat.card_pos).trans hb
  apply hn c.innerSize ((constraintNetwork I Acc c).readRedundancy L)
    (Compiler.Vertex c.program c.outputs) (Compiler.Edge c.program c.outputs)
    (constraintNetwork I Acc c).toMultigraph
    (Compiler.connected I _) (Compiler.loopless I _) (Compiler.maxDegreeLE I _ le_rfl hfan)
  · simpa [Circuit.innerSize] using Compiler.card_vertex_le (out := c.outputs) hfan
  · simpa only [Nat.reduceSub, one_mul, Module.finrank_pi, Fintype.card_fin] using
      cycleRank_add_redundancy_le_of_linear_inputs I Acc c L hfan hf
        ((Nat.le_self_pow two_ne_zero _).trans hbig) hc
  · intro π w hw
    simpa only [Nat.cast_ofNat, Nat.cast_add, show (2 : ℝ) + 2 = 4 by norm_num] using
      logb_ncard_le_of_linear_inputs I Acc c L le_rfl hfan hf hbig hc π hw

/-- Sublinear redundancy of the reached linear forms preserves the entire
leading coefficient, even with arbitrarily many unused supplied inputs. -/
theorem lowerBound_linear_inputs_of_sublinear_redundancy {F : Type u} [Field F] [Finite F]
    {A : ℝ} (hA : 0 < A) (hA1 : A ≤ 1) (hlayout : LayoutBound 3 A)
    (S : ∀ n, Set (Fin n → F)) (K b : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, SumsetFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card F) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    (hb : (fun n => (b n : ℝ)) =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (m : ℕ) (σ : Signature.{v}) (I : Interpretation σ F) (Acc : Set F)
      (c : Circuit σ m 1) (L : (Fin n → F) →ₗ[F] (Fin m → F)), c.FanInAtMost 2 →
      (∀ x, c.eval I (L x) 0 ∈ Acc ↔ x ∈ S n) →
      (constraintNetwork I Acc c).readRedundancy L ≤ b n →
        (1 + 1 / A - ε) * n < c.innerSize := by
  have hcoef : 0 ≤ 1 / A - 1 := sub_nonneg.mpr ((le_div_iff₀ hA).mpr (by simpa using hA1))
  filter_upwards [lowerBound_linear_inputs hA hA1 hlayout S K hfree hK hdense
    (half_pos hε), (hb.const_mul_left (1 / A - 1)).bound (half_pos hε)] with n hn hbnd
  intro m σ I Acc c L hfan hc hr
  have h := hn m σ I Acc c L hfan hc
  have hr' : (1 / A - 1) * ((constraintNetwork I Acc c).readRedundancy L : ℝ) ≤
      (1 / A - 1) * (b n : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hr) hcoef
  have hbnd' : (1 / A - 1) * (b n : ℝ) ≤ ε / 2 * n := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] using
      (le_abs_self _).trans hbnd
  linarith

/-- A sublinear total code codimension suffices. In particular an injective
encoding `x ↦ (x, Lx)` with `o(n)` supplied parities preserves the coefficient. -/
theorem lowerBound_linear_inputs_of_sublinear_codimension {F : Type u} [Field F] [Finite F]
    {A : ℝ} (hA : 0 < A) (hA1 : A ≤ 1) (hlayout : LayoutBound 3 A)
    (S : ∀ n, Set (Fin n → F)) (K b : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, SumsetFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card F) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    (hb : (fun n => (b n : ℝ)) =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (m : ℕ) (σ : Signature.{v}) (I : Interpretation σ F) (Acc : Set F)
      (c : Circuit σ m 1) (L : (Fin n → F) →ₗ[F] (Fin m → F)), c.FanInAtMost 2 →
      (∀ x, c.eval I (L x) 0 ∈ Acc ↔ x ∈ S n) →
      m - Module.finrank F (LinearMap.range L) ≤ b n →
        (1 + 1 / A - ε) * n < c.innerSize := by
  filter_upwards [lowerBound_linear_inputs_of_sublinear_redundancy hA hA1 hlayout S K b
    hfree hK hdense hb hε] with n hn
  intro m σ I Acc c L hfan hc hcodim
  apply hn m σ I Acc c L hfan hc
  have h := LinearBoundary.ncard_sub_coordinateRank_le_codim L (constraintNetwork I Acc c).read
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact h.trans hcodim

end Frontier
