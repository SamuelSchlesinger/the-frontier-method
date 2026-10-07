/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Transferring distributional bounds to randomized computation

Independent input and seed measures may be nonuniform and have infinite support. Tonelli's
theorem transfers any almost-everywhere bound on the input average of a nonnegative payoff
to the randomized average. The bound may depend on the seed. Probability measures give the
usual constant-bound and worst-input consequences.

This is the averaging direction of Yao's principle, not the minimax equality. No circuit
model, Boolean output, or uniform distribution is required. A correctness relation specializes
the payoff to its indicator; it can describe decision, search, or approximation problems.

Reference: Avrim Blum and Manuel Blum, *15-451 Algorithms*, Fall 2006, Section 5.4,
https://www.cs.cmu.edu/~avrim/451f06/lectures/lects1-10.pdf.
-/

@[expose] public section

namespace Frontier.Randomized

open MeasureTheory Set
open scoped ENNReal

variable {X R : Type*} [MeasurableSpace X] [MeasurableSpace R]
  {μ : Measure X} {ν : Measure R}

/-- Independent randomization preserves seedwise bounds on any nonnegative payoff.
Both measures may be unnormalized, and the bound may vary with the seed. -/
theorem average_le [SFinite μ] [SFinite ν] {payoff : X → R → ℝ≥0∞}
    (hm : AEMeasurable (Function.uncurry payoff) (μ.prod ν)) {bound : R → ℝ≥0∞}
    (h : ∀ᵐ r ∂ν, ∫⁻ x, payoff x r ∂μ ≤ bound r) :
    ∫⁻ x, ∫⁻ r, payoff x r ∂ν ∂μ ≤ ∫⁻ r, bound r ∂ν := by
  rw [lintegral_lintegral_swap hm]
  exact lintegral_mono_ae h

/-- A common bound on almost every deterministic choice also bounds its random mixture. -/
theorem average_le_const [SFinite μ] [IsProbabilityMeasure ν] {payoff : X → R → ℝ≥0∞}
    (hm : AEMeasurable (Function.uncurry payoff) (μ.prod ν)) {bound : ℝ≥0∞}
    (h : ∀ᵐ r ∂ν, ∫⁻ x, payoff x r ∂μ ≤ bound) :
    ∫⁻ x, ∫⁻ r, payoff x r ∂ν ∂μ ≤ bound := by
  simpa using average_le hm h

/-- Some input performs no better than the common deterministic average bound. -/
theorem exists_input_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {payoff : X → R → ℝ≥0∞}
    (hm : AEMeasurable (Function.uncurry payoff) (μ.prod ν)) {bound : ℝ≥0∞}
    (h : ∀ᵐ r ∂ν, ∫⁻ x, payoff x r ∂μ ≤ bound) :
    ∃ x, ∫⁻ r, payoff x r ∂ν ≤ bound := by
  obtain ⟨x, hx⟩ := exists_le_lintegral hm.lintegral_prod_right
  exact ⟨x, hx.trans (average_le_const hm h)⟩

/-- Fixing a seed can preserve average performance and any almost-sure admissibility
condition. Finiteness rules out an unattained infinite average. -/
theorem exists_seed [SFinite μ] [IsProbabilityMeasure ν] {payoff : X → R → ℝ≥0∞}
    (hm : AEMeasurable (Function.uncurry payoff) (μ.prod ν))
    (hfin : ∫⁻ x, ∫⁻ r, payoff x r ∂ν ∂μ ≠ ∞)
    {P : R → Prop} (hP : ∀ᵐ r ∂ν, P r) :
    ∃ r, P r ∧ (∫⁻ x, ∫⁻ t, payoff x t ∂ν ∂μ) ≤ ∫⁻ x, payoff x r ∂μ := by
  rw [lintegral_lintegral_swap hm] at hfin ⊢
  obtain ⟨r, hr, havg⟩ := exists_notMem_null_lintegral_le hfin (ae_iff.mp hP)
  exact ⟨r, by simpa using hr, havg⟩

/-- Average success over independent inputs and seeds is unchanged by swapping the averages. -/
theorem success_eq_average [SFinite μ] [SFinite ν] {correct : X → R → Prop}
    (hm : MeasurableSet {p : X × R | correct p.1 p.2}) :
    (∫⁻ x, ν {r | correct x r} ∂μ) = ∫⁻ r, μ {x | correct x r} ∂ν :=
  (Measure.prod_apply hm).symm.trans (Measure.prod_apply_symm hm)

/-- Any common distributional success bound survives independent randomization. -/
theorem success_le [SFinite μ] [IsProbabilityMeasure ν] {correct : X → R → Prop}
    (hm : MeasurableSet {p : X × R | correct p.1 p.2}) {bound : ℝ≥0∞}
    (h : ∀ᵐ r ∂ν, μ {x | correct x r} ≤ bound) :
    ∫⁻ x, ν {r | correct x r} ∂μ ≤ bound := by
  rw [success_eq_average hm]
  exact lintegral_le_const h

/-- Black-box transfer for any class of deterministic maps and any correctness relation.
Only almost every sampled map must belong to the class. -/
theorem success_le_of_class [SFinite μ] [IsProbabilityMeasure ν]
    {Y : Type*} {C : Set (X → Y)} {correct : X → Y → Prop} {run : R → X → Y}
    (hm : MeasurableSet {p : X × R | correct p.1 (run p.2 p.1)}) {bound : ℝ≥0∞}
    (hC : ∀ g ∈ C, μ {x | correct x (g x)} ≤ bound) (hrun : ∀ᵐ r ∂ν, run r ∈ C) :
    ∫⁻ x, ν {r | correct x (run r x)} ∂μ ≤ bound :=
  success_le hm (hrun.mono fun _ hr => hC _ hr)

/-- The randomized algorithm fails to exceed the deterministic bound on some input. -/
theorem exists_input_success_le [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {correct : X → R → Prop} (hm : MeasurableSet {p : X × R | correct p.1 p.2})
    {bound : ℝ≥0∞} (h : ∀ᵐ r ∂ν, μ {x | correct x r} ≤ bound) :
    ∃ x, ν {r | correct x r} ≤ bound := by
  obtain ⟨x, hx⟩ := exists_le_lintegral (μ := μ)
    (measurable_measure_prodMk_left (ν := ν) hm).aemeasurable
  exact ⟨x, hx.trans (success_le hm h)⟩

/-- Some admissible fixed seed is at least as successful on average as the randomized
algorithm. This is a distributional conclusion, not simultaneous success on every input. -/
theorem exists_seed_success_ge [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {correct : X → R → Prop} (hm : MeasurableSet {p : X × R | correct p.1 p.2})
    {P : R → Prop} (hP : ∀ᵐ r ∂ν, P r) :
    ∃ r, P r ∧ (∫⁻ x, ν {t | correct x t} ∂μ) ≤ μ {x | correct x r} := by
  rw [success_eq_average hm]
  have hfin : ∫⁻ r, μ {x | correct x r} ∂ν ≠ ∞ :=
    ne_of_lt ((lintegral_le_const (Filter.Eventually.of_forall fun _ => prob_le_one)).trans_lt
      ENNReal.one_lt_top)
  obtain ⟨r, hr, havg⟩ := exists_notMem_null_lintegral_le hfin (ae_iff.mp hP)
  exact ⟨r, by simpa using hr, havg⟩

end Frontier.Randomized
