/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.AverageCase.Capacity

/-!
# Conditional potentials for transition encodings

The states at depth `t` are prefixes of an encoding, not successive graph cuts.
Their masses are obtained from the actual joint distribution of a transition.
A potential satisfying the displayed local inequalities bounds the final square-root
moment by telescoping. This allows dependencies and history-dependent charges; replacing
the conditional distributions by independent signal marginals is not valid.

This is a certificate interface. A universal circuit bound on its initial potential
remains a separate requirement.
-/

@[expose] public section

namespace Frontier.Communication

variable {State : ℕ → Type*} [∀ t, Fintype (State t)]

/-- Sum of square-root masses weighted by a prefix potential. -/
noncomputable def rootPotential (mass potential : ∀ t, State t → ℝ) (t : ℕ) : ℝ :=
  ∑ u, Real.sqrt (mass t u) * potential t u

open Classical in
/-- A local conditional certificate can charge one prefix by all its refinements. -/
theorem rootPotential_step (mass potential : ∀ t, State t → ℝ)
    (parent : ∀ t, State (t + 1) → State t) (t : ℕ)
    (h : ∀ u, (∑ v with parent t v = u,
        Real.sqrt (mass (t + 1) v) * potential (t + 1) v) ≤
      Real.sqrt (mass t u) * potential t u) :
    rootPotential mass potential (t + 1) ≤ rootPotential mass potential t := by
  classical
  unfold rootPotential
  rw [← Finset.sum_fiberwise Finset.univ (parent t)
    (fun v => Real.sqrt (mass (t + 1) v) * potential (t + 1) v)]
  exact Finset.sum_le_sum fun u _ => h u

open Classical in
/-- Local conditional certificates amortize over the whole encoding. With leaf potential
one and a single unit-mass root, this bounds the sum of square roots of codeword masses
by the root potential. -/
theorem rootPotential_le (mass potential : ∀ t, State t → ℝ)
    (parent : ∀ t, State (t + 1) → State t) (T : ℕ)
    (h : ∀ t < T, ∀ u, (∑ v with parent t v = u,
        Real.sqrt (mass (t + 1) v) * potential (t + 1) v) ≤
      Real.sqrt (mass t u) * potential t u) :
    rootPotential mass potential T ≤ rootPotential mass potential 0 := by
  induction T with
  | zero => exact le_rfl
  | succ T ih =>
    exact (rootPotential_step mass potential parent T (h T (by lia))).trans
      (ih fun t ht => h t (by lia))

open Classical in
/-- Two upper certificates on the same prefix tree may be combined pointwise.
At each child use the cheaper potential. The local inequality still holds, so
the choice can depend on the complete prefix without an independence hypothesis.
The two certificates must use the same masses and the same parent map. -/
theorem rootPotential_min_step (mass V W : ∀ t, State t → ℝ)
    (parent : ∀ t, State (t + 1) → State t) (t : ℕ)
    (hV : ∀ u, (∑ v with parent t v = u,
        Real.sqrt (mass (t + 1) v) * V (t + 1) v) ≤
      Real.sqrt (mass t u) * V t u)
    (hW : ∀ u, (∑ v with parent t v = u,
        Real.sqrt (mass (t + 1) v) * W (t + 1) v) ≤
      Real.sqrt (mass t u) * W t u) (u : State t) :
    (∑ v with parent t v = u,
        Real.sqrt (mass (t + 1) v) * min (V (t + 1) v) (W (t + 1) v)) ≤
      Real.sqrt (mass t u) * min (V t u) (W t u) := by
  rw [mul_min_of_nonneg _ _ (Real.sqrt_nonneg _)]
  apply le_min
  · exact (Finset.sum_le_sum fun v _ =>
      mul_le_mul_of_nonneg_left (min_le_left _ _) (Real.sqrt_nonneg _)).trans (hV u)
  · exact (Finset.sum_le_sum fun v _ =>
      mul_le_mul_of_nonneg_left (min_le_right _ _) (Real.sqrt_nonneg _)).trans (hW u)

open Classical in
/-- The pointwise minimum of compatible local certificates bounds the final
square-root moment whenever both leaf potentials are at least one. This theorem
records the telescoping inequality; a universal bound on its root remains open. -/
theorem rootPotential_min_le (mass V W : ∀ t, State t → ℝ)
    (parent : ∀ t, State (t + 1) → State t) (T : ℕ)
    (hV : ∀ t < T, ∀ u, (∑ v with parent t v = u,
        Real.sqrt (mass (t + 1) v) * V (t + 1) v) ≤
      Real.sqrt (mass t u) * V t u)
    (hW : ∀ t < T, ∀ u, (∑ v with parent t v = u,
        Real.sqrt (mass (t + 1) v) * W (t + 1) v) ≤
      Real.sqrt (mass t u) * W t u) :
    rootPotential mass (fun t u => min (V t u) (W t u)) T ≤
      rootPotential mass (fun t u => min (V t u) (W t u)) 0 :=
  rootPotential_le _ _ _ _ fun t ht =>
    rootPotential_min_step mass V W parent t (hV t ht) (hW t ht)

end Frontier.Communication
