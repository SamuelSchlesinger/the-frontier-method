/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Randomized.Circuit
public import Frontier.AverageCase.Extractor
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Randomized circuit lower bounds

The general averaging principle in `Frontier.Randomized.Basic` applies to any deterministic
class, any independent input and seed distributions, and any measurable correctness relation.
Here it is connected to uniform Boolean agreement and the existing circuit lower bounds.

A randomized circuit may have arbitrarily many coin ports and any joint distribution on
them; the coins need not be fair or mutually independent. They must be independent of the
ordinary input. Fixing the coins preserves fan-in and the positive-arity gate count, even
when the original basis has no constants. Only the explicit extractor construction remains
external to the formalization.
-/

@[expose] public section

namespace Frontier

open Cslib.Circuits MeasureTheory ProbabilityTheory Set Filter Asymptotics
open scoped ENNReal Topology

universe v

/-- The full layout-dependent average-case bound, with arbitrary random input ports. -/
theorem averageCase_randomized {A ε γ : ℝ} (hA : 0 < A) (hlayout : LayoutBound 3 A)
    (hε : 0 < ε) (hγ1 : γ < 1) (hγε : γ < A * ε)
    (f : ∀ n, (Fin n → Bool) → Bool) (K : ℕ → ℕ) (b : ℕ → ℝ)
    (hK2 : ∀ᶠ n in atTop, 1 < K n)
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hb : ∀ᶠ n in atTop, 0 ≤ b n)
    (hf : ∀ᶠ n in atTop, RectangleBias (f n) (K n) (2 * b n)) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ Bool)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 2 →
      (c.innerSize : ℝ) ≤ (1 + 1 / A - ε) * n →
      ∀ (ν : Measure (Fin k → Bool)) [IsProbabilityMeasure ν],
        (∫⁻ x, ν {y | f n x = c.eval I (Fin.append x y) 0} ∂uniformOn univ) ≤
            ENNReal.ofReal (1 / 2 + b n + (2 : ℝ) ^ (-γ * n)) ∧
          ∃ x, ν {y | f n x = c.eval I (Fin.append x y) 0} ≤
            ENNReal.ofReal (1 / 2 + b n + (2 : ℝ) ^ (-γ * n)) := by
  filter_upwards [averageCase hA hlayout hε hγ1 hγε f K b hK2 hK hb hf] with n hn
  intro k σ I c hfan hs ν _
  exact randomized_circuit_bound hn I c hfan hs ν

/-- The unconditional Gaussian coefficient applies to randomized circuits, with the same
average-success bound and an input witnessing that bound. -/
theorem averageCase_randomized_gaussian {ε : ℝ} (hε : 0 < ε)
    (f : ∀ n, (Fin n → Bool) → Bool) (K : ℕ → ℕ) (b : ℕ → ℝ)
    (hK2 : ∀ᶠ n in atTop, 1 < K n)
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hb : ∀ᶠ n in atTop, 0 ≤ b n)
    (hf : ∀ᶠ n in atTop, RectangleBias (f n) (K n) (2 * b n)) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v})
      (I : Interpretation σ Bool) (c : Circuit σ (n + k) 1), c.FanInAtMost 2 →
      (c.innerSize : ℝ) ≤
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n →
      ∀ (ν : Measure (Fin k → Bool)) [IsProbabilityMeasure ν],
        (∫⁻ x, ν {y | f n x = c.eval I (Fin.append x y) 0} ∂uniformOn univ) ≤
            ENNReal.ofReal (1 / 2 + b n + (2 : ℝ) ^ (-γ * n)) ∧
          ∃ x, ν {y | f n x = c.eval I (Fin.append x y) 0} ≤
            ENNReal.ofReal (1 / 2 + b n + (2 : ℝ) ^ (-γ * n)) := by
  obtain ⟨γ, hγ, h⟩ := averageCase_gaussian hε f K b hK2 hK hb hf
  refine ⟨γ, hγ, ?_⟩
  filter_upwards [h] with n hn
  intro k σ I c hfan hs ν _
  exact randomized_circuit_bound hn I c hfan hs ν

/-- With vanishing rectangle bias, any fixed worst-input success probability above `1/2`
requires the Gaussian gate lower bound, uniformly in the number and distribution of coins. -/
theorem lowerBound_randomized_gaussian {ε success : ℝ} (hε : 0 < ε)
    (hsuccess : 1 / 2 < success)
    (f : ∀ n, (Fin n → Bool) → Bool) (K : ℕ → ℕ) (b : ℕ → ℝ)
    (hK2 : ∀ᶠ n in atTop, 1 < K n)
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hb : ∀ᶠ n in atTop, 0 ≤ b n) (hb0 : Tendsto b atTop (𝓝 0))
    (hf : ∀ᶠ n in atTop, RectangleBias (f n) (K n) (2 * b n)) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ Bool)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 2 →
      ∀ (ν : Measure (Fin k → Bool)) [IsProbabilityMeasure ν],
        (∀ x, ENNReal.ofReal success ≤ ν {y | f n x = c.eval I (Fin.append x y) 0}) →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n <
          (c.innerSize : ℝ) := by
  obtain ⟨γ, hγ, h⟩ := averageCase_gaussian hε f K b hK2 hK hb hf
  have hexp : Tendsto (fun n : ℕ => (2 : ℝ) ^ (-γ * n)) atTop (𝓝 0) :=
    (tendsto_rpow_atBot_of_base_gt_one 2 (by norm_num)).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop_of_neg (neg_neg_of_pos hγ))
  have hlim : Tendsto (fun n => 1 / 2 + b n + (2 : ℝ) ^ (-γ * n))
      atTop (𝓝 (1 / 2 : ℝ)) := by
    simpa using ((tendsto_const_nhds (x := (1 / 2 : ℝ))).add hb0).add hexp
  filter_upwards [h, hlim.eventually_lt_const hsuccess] with n hn hgap
  intro k σ I c hfan ν _ hcorrect
  exact size_lt_of_randomized_correct hn I c hfan ν
    ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hgap) hcorrect

/-- Polynomially small extractor error gives the same randomized prediction advantage. -/
theorem averageCase_randomized_sumset_polynomial {ε : ℝ} (hε : 0 < ε)
    (f : ∀ n, (Fin n → Bool) → Bool) (K : ℕ → ℕ) (b : ℕ → ℝ)
    (hK2 : ∀ᶠ n in atTop, 1 < K n)
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hb : ∀ᶠ n in atTop, 0 ≤ b n)
    (hf : ∀ᶠ n in atTop, FlatSumsetBias (f n) (K n) (2 * b n))
    {α C : ℝ} (hpoly : ∀ᶠ n in atTop, b n ≤ C * (n : ℝ) ^ (-α)) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ Bool)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 2 →
      (c.innerSize : ℝ) ≤
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n →
      ∀ (ν : Measure (Fin k → Bool)) [IsProbabilityMeasure ν],
        (∫⁻ x, ν {y | f n x = c.eval I (Fin.append x y) 0} ∂uniformOn univ) ≤
            ENNReal.ofReal (1 / 2 + (C + 1) * (n : ℝ) ^ (-α)) ∧
          ∃ x, ν {y | f n x = c.eval I (Fin.append x y) 0} ≤
            ENNReal.ofReal (1 / 2 + (C + 1) * (n : ℝ) ^ (-α)) := by
  filter_upwards [averageCase_sumset_polynomial hε f K b hK2 hK hb hf hpoly] with n hn
  intro k σ I c hfan hs ν _
  exact randomized_circuit_bound hn I c hfan hs ν

end Frontier
