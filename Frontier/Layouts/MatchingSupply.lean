/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.MatchingGaussian
public import Frontier.Main

/-!
# A strict supply improvement from disjoint pairs

The improved cubic layout transfers through the existing compression and
frontier theorems. It gives a graph-independent circuit coefficient strictly
larger than the original Gaussian coefficient `L`. Quantitative covariance
stability certifies a cycle-rank saving of `10⁻⁴⁸` and a circuit-coefficient
gain of at least `10⁻⁴⁷`. This does not assert the target `5n-o(n)` or
preservation under arbitrarily many free redundant parity inputs.
-/

@[expose] public section

namespace Frontier

open Cslib.Circuits Filter Asymptotics Gaussian

universe u v

/-- Connected subcubic multigraphs admit a cycle-rank coefficient strictly below `2p`. -/
theorem exists_layoutBound_lt_gaussian :
    ∃ A : ℝ, 0 < A ∧ A < 2 * gaussianCoefficient ∧ LayoutBound 3 A := by
  obtain ⟨p, hp, hpg, hlayout⟩ := PairLayout.exists_cubicLayoutBound_lt_gaussian
  exact ⟨2 * p, mul_pos two_pos hp, mul_lt_mul_of_pos_left hpg two_pos,
    LayoutBound.of_cubic hp.le hlayout⟩

/-- A single improved constant works for every dense rectangle-free family,
over every finite nontrivial alphabet, with the original unrestricted binary circuit model. -/
theorem exists_lowerBound_gt_gaussian :
    ∃ L : ℝ, 1 + 1 / (2 * gaussianCoefficient) < L ∧
      ∀ {U : Type u} [Finite U] [Nontrivial U] (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ),
        (∀ᶠ n in atTop, RectangleFree (S n) (K n)) →
        (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)) →
        (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
          (fun n => (n : ℝ)) →
        ∀ {ε : ℝ}, 0 < ε →
          ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
            (c : Circuit σ n 1), c.FanInAtMost 2 → Decides c I Acc (S n) →
              (L - ε) * n < c.innerSize := by
  obtain ⟨A, hA, hAg, hlayout⟩ := exists_layoutBound_lt_gaussian
  refine ⟨1 + 1 / A, by linarith [one_div_lt_one_div_of_lt hA hAg],
    fun {U} _ _ S K hfree hK hdense {ε} hε => ?_⟩
  exact lowerBound_fanInTwo hA hlayout S K hfree hK hdense hε

/-- The explicit cycle-rank coefficient `2p - 10⁻⁴⁸`. -/
noncomputable def matchingLayoutCoefficient : ℝ :=
  2 * gaussianCoefficient - PairLayout.matchingMeanSaving

theorem matchingLayoutCoefficient_pos : 0 < matchingLayoutCoefficient := by
  dsimp [matchingLayoutCoefficient, PairLayout.matchingMeanSaving]
  linarith [two_mul_gaussianCoefficient_ge]

/-- The explicit improved coefficient for unrestricted binary circuits. -/
noncomputable def matchingCircuitCoefficient : ℝ := 1 + 1 / matchingLayoutCoefficient

/-- The quantitative matching construction supplies `2p - 10⁻⁴⁸` for all
connected subcubic multigraphs. -/
theorem layoutBound_matching_explicit : LayoutBound 3 matchingLayoutCoefficient := by
  have hp : 0 ≤ gaussianCoefficient - PairLayout.matchingMeanSaving / 2 := by
    linarith [matchingLayoutCoefficient_pos,
      show matchingLayoutCoefficient = 2 * gaussianCoefficient - PairLayout.matchingMeanSaving
        from rfl]
  have h := LayoutBound.of_cubic hp PairLayout.cubicLayoutBound_matching_explicit
  convert h using 1
  dsimp [matchingLayoutCoefficient]
  ring

/-- The explicit circuit coefficient improves the original Gaussian constant
by at least the exact rational number `10⁻⁴⁷`. -/
theorem matchingCircuitCoefficient_gain :
    1 + 1 / (2 * gaussianCoefficient) + 1 / 10 ^ 47 ≤ matchingCircuitCoefficient := by
  let a := 2 * gaussianCoefficient
  let η := PairLayout.matchingMeanSaving
  have ha : 0 < a := mul_pos two_pos gaussianCoefficient_pos
  have haη : 0 < a - η := matchingLayoutCoefficient_pos
  have hη : 0 < η := PairLayout.matchingMeanSaving_pos
  have hahi : a ≤ 9 / 32 := two_mul_gaussianCoefficient_le
  have ha2 : a * a ≤ (9 / 32 : ℝ) * (9 / 32) :=
    mul_le_mul hahi hahi ha.le (by norm_num)
  have hden : 0 < a * (a - η) := mul_pos ha haη
  have hdenhi : a * (a - η) ≤ 1 / 10 := by
    nlinarith [mul_nonneg ha.le hη.le]
  have he : 1 / (a - η) - 1 / a = η / (a * (a - η)) := by
    field_simp
    ring
  have hgain : 10 * η ≤ 1 / (a - η) - 1 / a := by
    rw [he, le_div_iff₀ hden]
    nlinarith only [mul_le_mul_of_nonneg_left hdenhi hη.le]
  have hnum : 10 * η = (1 : ℝ) / 10 ^ 47 := by
    norm_num [η, PairLayout.matchingMeanSaving]
  rw [hnum] at hgain
  change 1 + 1 / a + 1 / 10 ^ 47 ≤ 1 + 1 / (a - η)
  linarith only [hgain]

/-- The explicit improved lower bound, with the same dense rectangle-free
families and unrestricted binary circuit model as the original Gaussian theorem. -/
theorem lowerBound_matching_explicit {U : Type u} [Finite U] [Nontrivial U]
    (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] (fun n => (n : ℝ)))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      (fun n => (n : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → Decides c I Acc (S n) →
        (matchingCircuitCoefficient - ε) * n < c.innerSize :=
  lowerBound_fanInTwo matchingLayoutCoefficient_pos layoutBound_matching_explicit
    S K hfree hK hdense hε

end Frontier
