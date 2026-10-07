/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Randomized.Basic
public import Frontier.ForCslib.Restriction
public import Frontier.AverageCase.Bias
public import Mathlib.Probability.UniformOn

/-!
# From deterministic agreement to randomized circuits

This finite interface needs no graph layout or extractor theorem. The steps are:

1. Identify uniform probability with the existing `agreement` counting definition.
2. Fix the random input ports without changing positive-arity size or fan-in.
3. Apply the general averaging theorem to any deterministic agreement bound.

`randomized_circuit_bound` gives both an average bound and a bad input.
`size_lt_of_randomized_correct` turns these into a gate lower bound for any larger
worst-input success target. The seed law is independent of the ordinary input; its
coordinates may be biased and mutually dependent.
-/

@[expose] public section

namespace Frontier

open Cslib.Circuits MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

universe v

variable {X R : Type*} [MeasurableSpace X] [MeasurableSpace R]

/-- Uniform measure agrees with the existing normalized counting definition. -/
theorem uniformOn_agreement [Finite X] [Nonempty X] [MeasurableSingletonClass X]
    (f g : X → Bool) :
    uniformOn univ {x | f x = g x} = ENNReal.ofReal (agreement f g) := by
  classical
  let := Fintype.ofFinite X
  have hpos : (0 : ℝ) < Nat.card X := by exact_mod_cast Nat.card_pos
  rw [uniformOn_univ, Measure.count_apply_finite _ (toFinite _)]
  rw [← ncard_eq_toFinset_card, agreement, ENNReal.ofReal_div_of_pos hpos]
  simp [Nat.card_eq_fintype_card]

/-- Uniform-input agreement bounds are closed under arbitrary independent random mixtures. -/
theorem randomized_agreement_le [Finite X] [Nonempty X] [MeasurableSingletonClass X]
    {ν : Measure R} [IsProbabilityMeasure ν] {f : X → Bool} {run : R → X → Bool}
    (hm : MeasurableSet {p : X × R | f p.1 = run p.2 p.1}) {bound : ℝ}
    (h : ∀ᵐ r ∂ν, agreement f (run r) ≤ bound) :
    ∫⁻ x, ν {r | f x = run r x} ∂uniformOn univ ≤ ENNReal.ofReal bound := by
  apply Randomized.success_le hm
  filter_upwards [h] with r hr
  rw [uniformOn_agreement]
  exact ENNReal.ofReal_le_ofReal hr

/-- A distributional bound supplies an input on which the randomized circuit does no better. -/
theorem exists_input_randomized_agreement_le [Finite X] [Nonempty X]
    [MeasurableSingletonClass X] {ν : Measure R} [IsProbabilityMeasure ν]
    {f : X → Bool} {run : R → X → Bool}
    (hm : MeasurableSet {p : X × R | f p.1 = run p.2 p.1}) {bound : ℝ}
    (h : ∀ᵐ r ∂ν, agreement f (run r) ≤ bound) :
    ∃ x, ν {r | f x = run r x} ≤ ENNReal.ofReal bound := by
  apply Randomized.exists_input_success_le (μ := uniformOn univ) hm
  filter_upwards [h] with r hr
  rw [uniformOn_agreement]
  exact ENNReal.ofReal_le_ofReal hr

/-- Any uniform agreement bound for deterministic circuits transfers to a circuit with
random input ports, without restrictions on the number or joint distribution of its coins. -/
theorem randomized_circuit_bound {n k r : ℕ} {f : (Fin n → Bool) → Bool} {size bound : ℝ}
    (h : ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (c : Circuit σ n 1),
      c.FanInAtMost r → (c.innerSize : ℝ) ≤ size →
        agreement f (fun x => c.eval I x 0) ≤ bound)
    {σ : Signature.{v}} (I : Interpretation σ Bool) (c : Circuit σ (n + k) 1)
    (hfan : c.FanInAtMost r) (hs : (c.innerSize : ℝ) ≤ size)
    (ν : Measure (Fin k → Bool)) [IsProbabilityMeasure ν] :
    (∫⁻ x, ν {y | f x = c.eval I (Fin.append x y) 0} ∂uniformOn univ) ≤
        ENNReal.ofReal bound ∧
      ∃ x, ν {y | f x = c.eval I (Fin.append x y) 0} ≤ ENNReal.ofReal bound := by
  have hm : MeasurableSet {p : (Fin n → Bool) × (Fin k → Bool) |
      f p.1 = c.eval I (Fin.append p.1 p.2) 0} := (toFinite _).measurableSet
  have hfix : ∀ᵐ y ∂ν, agreement f (fun x => c.eval I (Fin.append x y) 0) ≤ bound := by
    apply Eventually.of_forall
    intro y
    simpa only [Circuit.eval_fixInputs, Circuit.innerSize_fixInputs] using
      h σ.withBoolConstants I.withBoolConstants (c.fixInputs y) (hfan.fixInputs y)
        (by simpa only [Circuit.innerSize_fixInputs] using hs)
  exact ⟨randomized_agreement_le hm hfix, exists_input_randomized_agreement_le hm hfix⟩

/-- A randomized circuit succeeding on every input above the deterministic agreement bound
must exceed the same size budget. The success target and coin distribution are arbitrary. -/
theorem size_lt_of_randomized_correct {n k r : ℕ} {f : (Fin n → Bool) → Bool}
    {size bound : ℝ}
    (h : ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (c : Circuit σ n 1),
      c.FanInAtMost r → (c.innerSize : ℝ) ≤ size →
        agreement f (fun x => c.eval I x 0) ≤ bound)
    {σ : Signature.{v}} (I : Interpretation σ Bool) (c : Circuit σ (n + k) 1)
    (hfan : c.FanInAtMost r) (ν : Measure (Fin k → Bool)) [IsProbabilityMeasure ν]
    {success : ℝ≥0∞} (hgap : ENNReal.ofReal bound < success)
    (hcorrect : ∀ x, success ≤ ν {y | f x = c.eval I (Fin.append x y) 0}) :
    size < (c.innerSize : ℝ) := by
  by_contra! hs
  obtain ⟨x, hx⟩ := (randomized_circuit_bound h I c hfan hs ν).2
  exact (not_lt_of_ge ((hcorrect x).trans hx)) hgap

end Frontier
