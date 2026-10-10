/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Parity.LowerBound
public import Frontier.Layouts.MatchingSupply

/-!
# Preserving the old coefficient at a positive redundancy rate

The strict matching improvement creates a fixed gap above the old Gaussian
circuit coefficient. The explicit read-redundancy loss can spend part of this
gap. Consequently there exists a positive rate `γ`, uniform in the hard family
and field, such that `readRedundancy ≤ γ n` preserves the old coefficient.

The quantitative matching estimate certifies `γ = 10⁻⁴⁸`. This does not preserve
the entire improved coefficient at a positive rate or establish preservation
for an arbitrary linear number of free redundant inputs.
-/

@[expose] public section

namespace Frontier

open Set Filter Asymptotics Cslib.Circuits Gaussian

universe u v

/-- A redundancy rate of `10⁻⁴⁸` preserves the entire old Gaussian coefficient.
Correctness is required only on the supplied linear input image. -/
theorem linear_redundancy_rate_preserving_gaussian_explicit :
    ∀ {F : Type u} [Field F] [Finite F] (S : ∀ n, Set (Fin n → F)) (K : ℕ → ℕ),
      (∀ᶠ n in atTop, SumsetFree (S n) (K n)) →
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
      (fun n => n * Real.log (Nat.card F) - Real.log (S n).ncard) =o[atTop]
        (fun n => (n : ℝ)) →
        ∀ᶠ n in atTop, ∀ (m : ℕ) (σ : Signature.{v}) (I : Interpretation σ F) (Acc : Set F)
          (c : Circuit σ m 1) (L : (Fin n → F) →ₗ[F] (Fin m → F)), c.FanInAtMost 2 →
          (∀ x, c.eval I (L x) 0 ∈ Acc ↔ x ∈ S n) →
          ((constraintNetwork I Acc c).readRedundancy L : ℝ) ≤ PairLayout.matchingMeanSaving * n →
            (1 + 1 / (2 * gaussianCoefficient)) * n < c.innerSize := by
  have hA := matchingLayoutCoefficient_pos
  have hAlo : 1 / 10 ≤ matchingLayoutCoefficient := by
    dsimp [matchingLayoutCoefficient, PairLayout.matchingMeanSaving]
    linarith [two_mul_gaussianCoefficient_ge]
  have hAhi : matchingLayoutCoefficient < 1 := by
    dsimp [matchingLayoutCoefficient]
    linarith [two_mul_gaussianCoefficient_le, PairLayout.matchingMeanSaving_pos]
  have hD : 0 ≤ 1 / matchingLayoutCoefficient - 1 := by
    have h : 1 ≤ 1 / matchingLayoutCoefficient :=
      (le_div_iff₀ hA).mpr (by simpa using hAhi.le)
    linarith
  have hDhi : 1 / matchingLayoutCoefficient - 1 ≤ 9 := by
    have h : 1 / matchingLayoutCoefficient ≤ 10 := (div_le_iff₀ hA).mpr (by linarith)
    linarith
  have hgain : 1 + 1 / (2 * gaussianCoefficient) + 10 * PairLayout.matchingMeanSaving ≤
      matchingCircuitCoefficient := by
    convert matchingCircuitCoefficient_gain using 1
    norm_num [PairLayout.matchingMeanSaving]
  intro F _ _ S K hfree hK hdense
  filter_upwards [lowerBound_linear_inputs hA hAhi.le layoutBound_matching_explicit
    S K hfree hK hdense PairLayout.matchingMeanSaving_pos] with n hn
  intro m σ I Acc c L hfan hc hr
  have h := hn m σ I Acc c L hfan hc
  have hcost := mul_le_mul_of_nonneg_left hr hD
  have hpay := mul_le_mul_of_nonneg_right hDhi
    (mul_nonneg PairLayout.matchingMeanSaving_pos.le (Nat.cast_nonneg n))
  have hgain' := mul_le_mul_of_nonneg_right hgain (Nat.cast_nonneg n)
  dsimp [matchingCircuitCoefficient] at hgain'
  nlinarith only [h, hcost, hpay, hgain']

/-- A fixed positive linear redundancy rate preserves the entire old Gaussian
coefficient. Correctness is required only on the supplied linear input image. -/
theorem exists_linear_redundancy_rate_preserving_gaussian :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ {F : Type u} [Field F] [Finite F] (S : ∀ n, Set (Fin n → F)) (K : ℕ → ℕ),
        (∀ᶠ n in atTop, SumsetFree (S n) (K n)) →
        (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
        (fun n => n * Real.log (Nat.card F) - Real.log (S n).ncard) =o[atTop]
          (fun n => (n : ℝ)) →
          ∀ᶠ n in atTop, ∀ (m : ℕ) (σ : Signature.{v}) (I : Interpretation σ F) (Acc : Set F)
            (c : Circuit σ m 1) (L : (Fin n → F) →ₗ[F] (Fin m → F)), c.FanInAtMost 2 →
            (∀ x, c.eval I (L x) 0 ∈ Acc ↔ x ∈ S n) →
            ((constraintNetwork I Acc c).readRedundancy L : ℝ) ≤ γ * n →
              (1 + 1 / (2 * gaussianCoefficient)) * n < c.innerSize :=
  ⟨PairLayout.matchingMeanSaving, PairLayout.matchingMeanSaving_pos,
    linear_redundancy_rate_preserving_gaussian_explicit⟩

/-- Up to `10⁻⁴⁸ n` extra linear inputs may be supplied for free on consistent
pairs while retaining the full old Gaussian coefficient against the original `n`. -/
theorem free_parity_rate_preserving_gaussian_explicit :
    ∀ {F : Type u} [Field F] [Finite F] (S : ∀ n, Set (Fin n → F)) (K : ℕ → ℕ),
      (∀ᶠ n in atTop, SumsetFree (S n) (K n)) →
      (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
      (fun n => n * Real.log (Nat.card F) - Real.log (S n).ncard) =o[atTop]
        (fun n => (n : ℝ)) →
        ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ F) (Acc : Set F)
          (c : Circuit σ (n + k) 1) (L : (Fin n → F) →ₗ[F] (Fin k → F)), c.FanInAtMost 2 →
          (∀ x, c.eval I (fun i => parityInput L x (finSumFinEquiv.symm i)) 0 ∈ Acc ↔ x ∈ S n) →
          (k : ℝ) ≤ PairLayout.matchingMeanSaving * n →
            (1 + 1 / (2 * gaussianCoefficient)) * n < c.innerSize := by
  intro F _ _ S K hfree hK hdense
  filter_upwards [linear_redundancy_rate_preserving_gaussian_explicit S K hfree hK hdense] with n hn
  intro k σ I Acc c L hfan hc hk
  let E := (LinearMap.funLeft F F
    (finSumFinEquiv : Fin n ⊕ Fin k ≃ Fin (n + k)).symm).comp (parityInputMap L)
  have hE : Function.Injective E := by
    intro x y hxy
    apply parityInput_injective L
    funext i
    have h := congrFun hxy (finSumFinEquiv i)
    simpa [E] using h
  have hrank : Module.finrank F (LinearMap.range E) = n := by
    rw [LinearMap.finrank_range_of_inj hE, Module.finrank_pi, Fintype.card_fin]
  have hread : (constraintNetwork I Acc c).readRedundancy E ≤ k := by
    have h := LinearBoundary.ncard_sub_coordinateRank_le_codim E (constraintNetwork I Acc c).read
    rw [hrank, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    simpa [Network.readRedundancy] using h
  apply hn (n + k) σ I Acc c E hfan hc
  exact (by exact_mod_cast hread : ((constraintNetwork I Acc c).readRedundancy E : ℝ) ≤ k).trans hk

/-- In the user's consistent-pair model, some positive linear number of free
extra parities preserves the old coefficient. Their computation is not charged. -/
theorem exists_free_parity_rate_preserving_gaussian :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ {F : Type u} [Field F] [Finite F] (S : ∀ n, Set (Fin n → F)) (K : ℕ → ℕ),
        (∀ᶠ n in atTop, SumsetFree (S n) (K n)) →
        (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
        (fun n => n * Real.log (Nat.card F) - Real.log (S n).ncard) =o[atTop]
          (fun n => (n : ℝ)) →
          ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ F) (Acc : Set F)
            (c : Circuit σ (n + k) 1) (L : (Fin n → F) →ₗ[F] (Fin k → F)), c.FanInAtMost 2 →
            (∀ x, c.eval I (fun i => parityInput L x (finSumFinEquiv.symm i)) 0 ∈ Acc ↔ x ∈ S n) →
            (k : ℝ) ≤ γ * n → (1 + 1 / (2 * gaussianCoefficient)) * n < c.innerSize :=
  ⟨PairLayout.matchingMeanSaving, PairLayout.matchingMeanSaving_pos,
    free_parity_rate_preserving_gaussian_explicit⟩

end Frontier
