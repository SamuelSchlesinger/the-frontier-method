/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.Gaussian
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Gaussian vertex layouts in bounded degree

Normalize the truncated radial kernel at each vertex, take its Gaussian score, and sort.
Every edge crosses a fixed threshold with probability at most `arccos(ρ) / π`
(`measureReal_crossingEvent_le`); the limiting coefficient `vertexCoefficient d` is
`arccos (2 √(d - 1) / d) / π`, exactly `1/6` at degree four. The sampling argument that turns
this into a layout, with parallel edges retained, is `Frontier.Layouts.MultiGaussian`.
-/

@[expose] public section

namespace Frontier.Gaussian

open MeasureTheory ProbabilityTheory Finset

variable {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- A vertex's unit radial-kernel Gaussian score. -/
noncomputable def vertexScore (q : ℝ) (R : ℕ) (ω : W → ℝ) (v : W) : ℝ :=
  form (unitKernel H q R v) ω

def vertexEvent (q : ℝ) (R : ℕ) (p : ℝ → Prop) (v : W) : Set (W → ℝ) :=
  {ω | p (vertexScore H q R ω v)}

def crossingEvent (q : ℝ) (R : ℕ) (t : ℝ) : Sym2 W → Set (W → ℝ) :=
  Sym2.lift ⟨fun u v => {ω | Between t (vertexScore H q R ω u) (vertexScore H q R ω v)},
    fun _ _ => by ext ω; simp only [Set.mem_ofPred_eq, Between, or_comm]⟩

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem measurableSet_vertexEvent (q : ℝ) (R : ℕ) {p : ℝ → Prop}
    (hp : MeasurableSet {x | p x}) (v : W) : MeasurableSet (vertexEvent H q R p v) :=
  measurable_form _ hp

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem measurableSet_crossingEvent (q : ℝ) (R : ℕ) (t : ℝ) (e : Sym2 W) :
    MeasurableSet (crossingEvent H q R t e) := by
  induction e using Sym2.ind with
  | _ u v => exact measurableSet_between (measurable_form _) (measurable_form _) t

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem vertexScore_congr (q : ℝ) (R : ℕ) (v : W) {ω ω' : W → ℝ}
    (h : ∀ z ∈ ball H v R, ω z = ω' z) : vertexScore H q R ω v = vertexScore H q R ω' v :=
  form_congr (fun _z hz => unitKernel_eq_zero_of_notMem_ball H hz) h

omit [DecidableEq W] [DecidableRel H.Adj] in
theorem dependsOn_vertexEvent (q : ℝ) (R : ℕ) (p : ℝ → Prop) (v : W) :
    DependsOn (· ∈ vertexEvent H q R p v) (ball H v R : Set W) := by
  intro ω ω' h
  simp only [vertexEvent, Set.mem_ofPred_eq]
  rw [vertexScore_congr H q R v h]

omit [DecidableRel H.Adj] in
theorem dependsOn_crossingEvent (q : ℝ) (R : ℕ) (t : ℝ) (e : Sym2 W) :
    DependsOn (· ∈ crossingEvent H q R t e) (edgeSupport H R e : Set W) := by
  induction e using Sym2.ind with
  | _ u v =>
  intro ω ω' h
  change (Between t (vertexScore H q R ω u) (vertexScore H q R ω v)) =
    (Between t (vertexScore H q R ω' u) (vertexScore H q R ω' v))
  rw [vertexScore_congr H q R u (fun z hz => h z (mem_union.mpr (Or.inl hz))),
    vertexScore_congr H q R v (fun z hz => h z (mem_union.mpr (Or.inr hz)))]

omit [DecidableEq W] in
theorem measureReal_crossingEvent_le {d : ℕ} (hd : 2 ≤ d) (degree : ∀ v, H.degree v ≤ d)
    {q : ℝ} (hq : 0 ≤ q) (R : ℕ) {ρ : ℝ} (hρ0 : -1 < ρ)
    (hρ : ρ ≤ 2 * q / (1 + q ^ 2) - d * ((d - 1 : ℕ) * q ^ 2) ^ R)
    (t : ℝ) {e : Sym2 W} (he : e ∈ H.edgeFinset) :
    (gaussPi W).real (crossingEvent H q R t e) ≤ Real.arccos ρ / Real.pi := by
  induction e using Sym2.ind with
  | _ u v =>
  have hcorr := hρ.trans (sum_unitKernel_mul_ge_degree H hd degree hq R
    (SimpleGraph.mem_edgeFinset.mp he))
  exact (gaussPi_between_le_arccos (sum_unitKernel_sq H q R u) (sum_unitKernel_sq H q R v)
    (hρ0.trans_le hcorr) t).trans (div_le_div_of_nonneg_right
      (Real.arccos_le_arccos hcorr) Real.pi_pos.le)

/-- The per-edge crossing coefficient of Gaussian vertex scores in maximum degree `d`:
`arccos (2 √(d - 1) / d) / π`. -/
noncomputable def vertexCoefficient (d : ℕ) : ℝ := Real.arccos (vertexCorrelation d) / Real.pi

/-- Degree four gives an exact per-edge crossing coefficient of one sixth. -/
theorem vertexCoefficient_four : vertexCoefficient 4 = 1 / 6 := by
  have harg : vertexCorrelation 4 = Real.sqrt 3 / 2 := by norm_num [vertexCorrelation]; ring
  rw [vertexCoefficient, harg, ← Real.cos_pi_div_six,
    Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]
  field_simp

end Frontier.Gaussian
