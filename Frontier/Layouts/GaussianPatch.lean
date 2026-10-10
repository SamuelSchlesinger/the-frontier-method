/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.Gaussian
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Gaussian estimates for a two-vertex patch

A pair of adjacent cubic vertices has four outer ports. Optimizing the two
internal vertex colors yields an exact formula in pair-separation indicators,
including an intersection term. The latter can be bounded uniformly in the
threshold by conditioning on two independent Gaussian differences.

These are local estimates. A universal layout theorem additionally needs a
compatible collection of patches, the corresponding finite-graph score laws,
and concentration and tie bounds for one complete ordering.
-/

@[expose] public section

namespace Frontier.Gaussian

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- The cost of disagreeing with one binary port. -/
def portDisagreement (a b : Bool) : ℕ := if a = b then 0 else 1

/-- Cut cost of two adjacent vertices with four fixed outer port colors. -/
def twoVertexEnergy (a b c d u v : Bool) : ℕ :=
  portDisagreement u a + portDisagreement u b + portDisagreement u v +
    portDisagreement v c + portDisagreement v d

/-- Minimum cut cost inside the two-vertex patch. -/
def twoVertexCost (a b c d : Bool) : ℕ :=
  min (min (twoVertexEnergy a b c d false false) (twoVertexEnergy a b c d false true))
    (min (twoVertexEnergy a b c d true false) (twoVertexEnergy a b c d true true))

/-- The exact pair formula includes the event that both outer pairs straddle.
Clearing denominators keeps this combinatorial identity over natural numbers. -/
theorem four_mul_twoVertexCost (a b c d : Bool) :
    4 * twoVertexCost a b c d =
      2 * (portDisagreement a b + portDisagreement c d) +
      (portDisagreement a c + portDisagreement a d +
        portDisagreement b c + portDisagreement b d) +
      2 * portDisagreement a b * portDisagreement c d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- The cost is attained by a choice of the two internal colors. -/
theorem twoVertexCost_eq_minimum (a b c d : Bool) :
    (∃ u v, twoVertexEnergy a b c d u v = twoVertexCost a b c d) ∧
      ∀ u v, twoVertexCost a b c d ≤ twoVertexEnergy a b c d u v := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- Expected patch cost is an exact linear combination of six pair probabilities
and one simultaneous-separation probability. -/
theorem integral_twoVertexCost {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (a b c d : Ω → Bool)
    (ha : Measurable a) (hb : Measurable b) (hc : Measurable c) (hd : Measurable d) :
    (∫ ω, (twoVertexCost (a ω) (b ω) (c ω) (d ω) : ℝ) ∂μ) =
      (μ.real {ω | a ω ≠ b ω} + μ.real {ω | c ω ≠ d ω}) / 2 +
      ((μ.real {ω | a ω ≠ c ω} + μ.real {ω | a ω ≠ d ω}) +
        (μ.real {ω | b ω ≠ c ω} + μ.real {ω | b ω ≠ d ω})) / 4 +
      μ.real {ω | a ω ≠ b ω ∧ c ω ≠ d ω} / 2 := by
  classical
  let I (A : Set Ω) : Ω → ℝ := A.indicator (fun _ => 1)
  have hI {A : Set Ω} (hA : MeasurableSet A) : Integrable (I A) μ :=
    (integrable_const 1).indicator hA
  have hab : MeasurableSet {ω | a ω ≠ b ω} := (measurableSet_eq_fun ha hb).compl
  have hcd : MeasurableSet {ω | c ω ≠ d ω} := (measurableSet_eq_fun hc hd).compl
  have hac : MeasurableSet {ω | a ω ≠ c ω} := (measurableSet_eq_fun ha hc).compl
  have had : MeasurableSet {ω | a ω ≠ d ω} := (measurableSet_eq_fun ha hd).compl
  have hbc : MeasurableSet {ω | b ω ≠ c ω} := (measurableSet_eq_fun hb hc).compl
  have hbd : MeasurableSet {ω | b ω ≠ d ω} := (measurableSet_eq_fun hb hd).compl
  have hj : MeasurableSet {ω | a ω ≠ b ω ∧ c ω ≠ d ω} := hab.inter hcd
  have heq (ω : Ω) : (twoVertexCost (a ω) (b ω) (c ω) (d ω) : ℝ) =
      (I {ω | a ω ≠ b ω} ω + I {ω | c ω ≠ d ω} ω) / 2 +
      ((I {ω | a ω ≠ c ω} ω + I {ω | a ω ≠ d ω} ω) +
        (I {ω | b ω ≠ c ω} ω + I {ω | b ω ≠ d ω} ω)) / 4 +
      I {ω | a ω ≠ b ω ∧ c ω ≠ d ω} ω / 2 := by
    cases h₁ : a ω <;> cases h₂ : b ω <;> cases h₃ : c ω <;> cases h₄ : d ω <;>
      norm_num [I, Set.indicator, twoVertexCost, twoVertexEnergy, portDisagreement,
        h₁, h₂, h₃, h₄]
  simp_rw [heq]
  have hfirst := ((hI hab).add (hI hcd)).div_const 2
  have hleft := (hI hac).add (hI had)
  have hright := (hI hbc).add (hI hbd)
  have hcross := (hleft.add hright).div_const 4
  have hlast := (hI hj).div_const 2
  simp only [Pi.add_apply] at hfirst hcross
  have hfc := hfirst.add hcross
  simp only [Pi.add_def] at hfc hleft hright
  rw [integral_add hfc hlast, integral_add hfirst hcross,
    integral_div, integral_div, integral_div,
    integral_add (hI hab) (hI hcd),
    integral_add hleft hright,
    integral_add (hI hac) (hI had), integral_add (hI hbc) (hI hbd)]
  simp only [I, integral_indicator_const (1 : ℝ) hab, integral_indicator_const (1 : ℝ) hcd,
    integral_indicator_const (1 : ℝ) hac, integral_indicator_const (1 : ℝ) had,
    integral_indicator_const (1 : ℝ) hbc, integral_indicator_const (1 : ℝ) hbd,
    integral_indicator_const (1 : ℝ) hj, smul_eq_mul, mul_one]

/-- The binary port color at a threshold, with equality assigned to the upper side. -/
noncomputable def belowThreshold (t x : ℝ) : Bool := if x < t then true else false

theorem measurable_belowThreshold (t : ℝ) : Measurable (belowThreshold t) := by
  apply measurable_to_bool
  have heq : belowThreshold t ⁻¹' {true} = Iio t := by
    ext x
    by_cases hx : x < t <;> simp [belowThreshold, hx]
  rw [heq]
  exact measurableSet_Iio

theorem belowThreshold_ne_iff (t x y : ℝ) :
    belowThreshold t x ≠ belowThreshold t y ↔ Between t x y := by
  by_cases hx : x < t <;> by_cases hy : y < t <;>
    simp [belowThreshold, Between, hx, hy, not_le.mpr, le_of_not_gt]

/-- Conditioning on one Gaussian bounds a sheared rectangle by its area times
the product of the two peak densities. The shear and center are arbitrary. -/
theorem prod_gaussianReal_windows_le (s v : ℝ≥0) (hs : s ≠ 0) (hv : v ≠ 0)
    (c t w₁ w₂ : ℝ) :
    ((gaussianReal 0 s).prod (gaussianReal 0 v))
      {p : ℝ × ℝ | |p.1 + c * p.2 - t| ≤ w₁ ∧ |p.2 - t| ≤ w₂} ≤
      ENNReal.ofReal (2 * w₁ / Real.sqrt (2 * Real.pi * s)) *
        ENNReal.ofReal (2 * w₂ / Real.sqrt (2 * Real.pi * v)) := by
  have hmeas : MeasurableSet
      {p : ℝ × ℝ | |p.1 + c * p.2 - t| ≤ w₁ ∧ |p.2 - t| ≤ w₂} :=
    (measurableSet_le (f := fun p : ℝ × ℝ => |p.1 + c * p.2 - t|)
      (by fun_prop) measurable_const).inter
      (measurableSet_le (f := fun p : ℝ × ℝ => |p.2 - t|)
        (by fun_prop) measurable_const)
  rw [Measure.prod_apply_symm hmeas]
  let B := Icc (t - w₂) (t + w₂)
  have hslice (y : ℝ) :
      gaussianReal 0 s ((fun x => (x, y)) ⁻¹'
        {p : ℝ × ℝ | |p.1 + c * p.2 - t| ≤ w₁ ∧ |p.2 - t| ≤ w₂}) ≤
      B.indicator (fun _ => ENNReal.ofReal (2 * w₁ / Real.sqrt (2 * Real.pi * s))) y := by
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy]
      have hwin : |y - t| ≤ w₂ := by
        change t - w₂ ≤ y ∧ y ≤ t + w₂ at hy
        rw [abs_le]
        constructor <;> linarith [hy.1, hy.2]
      have heq : (fun x => (x, y)) ⁻¹'
          {p : ℝ × ℝ | |p.1 + c * p.2 - t| ≤ w₁ ∧ |p.2 - t| ≤ w₂} =
          Icc (t - c * y - w₁) (t - c * y + w₁) := by
        ext x
        change (|x + c * y - t| ≤ w₁ ∧ |y - t| ≤ w₂) ↔
          t - c * y - w₁ ≤ x ∧ x ≤ t - c * y + w₁
        simp only [hwin, and_true, abs_le]
        constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
      rw [heq]
      exact gaussianReal_Icc_le_length s hs (t - c * y) w₁
    · rw [indicator_of_notMem hy]
      have hempty : (fun x => (x, y)) ⁻¹'
          {p : ℝ × ℝ | |p.1 + c * p.2 - t| ≤ w₁ ∧ |p.2 - t| ≤ w₂} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        apply hy
        change t - w₂ ≤ y ∧ y ≤ t + w₂
        have hab := abs_le.mp hx.2
        constructor <;> linarith [hab.1, hab.2]
      simp [hempty]
  calc
    _ ≤ ∫⁻ y, B.indicator
        (fun _ => ENNReal.ofReal (2 * w₁ / Real.sqrt (2 * Real.pi * s))) y
          ∂gaussianReal 0 v := lintegral_mono hslice
    _ = ENNReal.ofReal (2 * w₁ / Real.sqrt (2 * Real.pi * s)) * gaussianReal 0 v B :=
      lintegral_indicator_const measurableSet_Icc _
    _ ≤ _ := by
      gcongr
      exact gaussianReal_Icc_le_length v hv t w₂

/-- The average of the interval-density bound against an independent Gaussian
half-width. No positivity assumption on either variance is needed here. -/
theorem lintegral_gaussianReal_window (s r : ℝ≥0) :
    ∫⁻ d, ENNReal.ofReal (2 * |d| / Real.sqrt (2 * Real.pi * s)) ∂gaussianReal 0 r =
      ENNReal.ofReal (4 * r /
        (Real.sqrt (2 * Real.pi * s) * Real.sqrt (2 * Real.pi * r))) := by
  have hi : Integrable (fun x : ℝ => |x|) (gaussianReal 0 r) := by
    simpa only [Real.norm_eq_abs, id_eq] using (memLp_id_gaussianReal 1).integrable le_rfl |>.norm
  have heq (d : ℝ) : 2 * |d| / Real.sqrt (2 * Real.pi * s) =
      (2 / Real.sqrt (2 * Real.pi * s)) * |d| := by ring
  simp_rw [heq, ENNReal.ofReal_mul (by positivity : 0 ≤ 2 / Real.sqrt (2 * Real.pi * s))]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun x => abs_nonneg x)),
    integral_abs_gaussianReal, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- Uniform bound for two Gaussian windows with independent Gaussian half-widths.
The two window centers may be correlated through a shear. -/
theorem prod_gaussianReal_double_window_le (s v r : ℝ≥0) (hs : s ≠ 0) (hv : v ≠ 0)
    (c t : ℝ) :
    (((gaussianReal 0 s).prod (gaussianReal 0 v)).prod
      ((gaussianReal 0 r).prod (gaussianReal 0 r)))
        {p : (ℝ × ℝ) × (ℝ × ℝ) |
          |p.1.1 + c * p.1.2 - t| ≤ |p.2.1| ∧ |p.1.2 - t| ≤ |p.2.2|} ≤
      ENNReal.ofReal (4 * r /
        (Real.sqrt (2 * Real.pi * s) * Real.sqrt (2 * Real.pi * r))) *
      ENNReal.ofReal (4 * r /
        (Real.sqrt (2 * Real.pi * v) * Real.sqrt (2 * Real.pi * r))) := by
  have hmeas : MeasurableSet {p : (ℝ × ℝ) × (ℝ × ℝ) |
      |p.1.1 + c * p.1.2 - t| ≤ |p.2.1| ∧ |p.1.2 - t| ≤ |p.2.2|} :=
    (measurableSet_le (f := fun p : (ℝ × ℝ) × (ℝ × ℝ) => |p.1.1 + c * p.1.2 - t|)
      (by fun_prop) (by fun_prop)).inter
      (measurableSet_le (f := fun p : (ℝ × ℝ) × (ℝ × ℝ) => |p.1.2 - t|)
        (by fun_prop) (by fun_prop))
  rw [Measure.prod_apply_symm hmeas]
  calc
    _ ≤ ∫⁻ d : ℝ × ℝ,
        ENNReal.ofReal (2 * |d.1| / Real.sqrt (2 * Real.pi * s)) *
        ENNReal.ofReal (2 * |d.2| / Real.sqrt (2 * Real.pi * v))
          ∂((gaussianReal 0 r).prod (gaussianReal 0 r)) := by
      apply lintegral_mono
      intro d
      exact prod_gaussianReal_windows_le s v hs hv c t |d.1| |d.2|
    _ = _ := by
      rw [lintegral_prod_mul
        (f := fun d : ℝ => ENNReal.ofReal (2 * |d| / Real.sqrt (2 * Real.pi * s)))
        (g := fun d : ℝ => ENNReal.ofReal (2 * |d| / Real.sqrt (2 * Real.pi * v)))
        (by fun_prop) (by fun_prop),
        lintegral_gaussianReal_window, lintegral_gaussianReal_window]

private theorem double_window_constant (s v r : ℝ≥0)
    (hs : s ≠ 0) (hv : v ≠ 0) (hr : r ≠ 0) :
    (4 * r / (Real.sqrt (2 * Real.pi * s) * Real.sqrt (2 * Real.pi * r))) *
      (4 * r / (Real.sqrt (2 * Real.pi * v) * Real.sqrt (2 * Real.pi * r))) =
        4 * r / (Real.pi ^ 2 * Real.sqrt ((s : ℝ) * v)) := by
  have hs' : 0 < (s : ℝ) := by positivity
  have hv' : 0 < (v : ℝ) := by positivity
  have hr' : 0 < (r : ℝ) := by positivity
  have hprod : Real.sqrt (2 * Real.pi * s) * Real.sqrt (2 * Real.pi * v) =
      2 * Real.pi * Real.sqrt ((s : ℝ) * v) := by
    calc
      _ = Real.sqrt ((2 * Real.pi * s) * (2 * Real.pi * v)) :=
        (Real.sqrt_mul (by positivity) _).symm
      _ = Real.sqrt ((2 * Real.pi) ^ 2 * ((s : ℝ) * v)) := by congr 1; ring
      _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi * (r : ℝ))
  rw [div_mul_div_comm]
  have hden :
      (Real.sqrt (2 * Real.pi * s) * Real.sqrt (2 * Real.pi * r)) *
        (Real.sqrt (2 * Real.pi * v) * Real.sqrt (2 * Real.pi * r)) =
      (2 * Real.pi * Real.sqrt ((s : ℝ) * v)) * (2 * Real.pi * r) := by
    calc
      _ = (Real.sqrt (2 * Real.pi * s) * Real.sqrt (2 * Real.pi * v)) *
          Real.sqrt (2 * Real.pi * r) ^ 2 := by ring
      _ = _ := by rw [hprod, hsq]
  rw [hden]
  field_simp
  ring

/-- If a threshold separates `u+d` and `u-d`, its distance to their center is
at most the absolute half-difference. -/
theorem abs_sub_le_of_between_add_sub {t u d : ℝ}
    (h : Between t (u + d) (u - d)) : |u - t| ≤ |d| := by
  rw [abs_le]
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
    constructor <;> linarith [le_abs_self d, neg_abs_le d]

/-- Two pairs whose centers have a Gaussian shear representation, with independent
Gaussian half-differences, straddle any fixed threshold with at most this probability.
In particular, this bound does not assume that the worst threshold is zero. -/
theorem prod_gaussianReal_double_straddle_le (s v r : ℝ≥0)
    (hs : s ≠ 0) (hv : v ≠ 0) (hr : r ≠ 0) (c t : ℝ) :
    (((gaussianReal 0 s).prod (gaussianReal 0 v)).prod
      ((gaussianReal 0 r).prod (gaussianReal 0 r))).real
        {p : (ℝ × ℝ) × (ℝ × ℝ) |
          Between t (p.1.1 + c * p.1.2 + p.2.1) (p.1.1 + c * p.1.2 - p.2.1) ∧
          Between t (p.1.2 + p.2.2) (p.1.2 - p.2.2)} ≤
      4 * r / (Real.pi ^ 2 * Real.sqrt ((s : ℝ) * v)) := by
  have h := prod_gaussianReal_double_window_le s v r hs hv c t
  rw [← ENNReal.ofReal_mul (by positivity), double_window_constant s v r hs hv hr] at h
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  apply le_trans (measure_mono ?_) h
  intro p hp
  exact ⟨abs_sub_le_of_between_add_sub hp.1, abs_sub_le_of_between_add_sub hp.2⟩

/-- Independent means and differences, represented on four standard Gaussian coordinates. -/
noncomputable def patchSample (s v r : ℝ≥0) (ω : (Fin 2 ⊕ Fin 2) → ℝ) :
    (ℝ × ℝ) × (ℝ × ℝ) :=
  ((Real.sqrt s * ω (.inl 0), Real.sqrt v * ω (.inl 1)),
    (Real.sqrt r * ω (.inr 0), Real.sqrt r * ω (.inr 1)))

/-- The four scaled coordinates have the product Gaussian law used in the window estimate. -/
theorem gaussPi_map_patchSample (s v r : ℝ≥0) :
    (gaussPi (Fin 2 ⊕ Fin 2)).map (patchSample s v r) =
      ((gaussianReal 0 s).prod (gaussianReal 0 v)).prod
        ((gaussianReal 0 r).prod (gaussianReal 0 r)) := by
  let σ : (Fin 2 ⊕ Fin 2) → ℝ≥0 := Sum.elim ![s, v] ![r, r]
  have hscale (i : Fin 2 ⊕ Fin 2) :
      MeasurePreserving (fun x : ℝ => Real.sqrt (σ i) * x)
        (gaussianReal 0 1) (gaussianReal 0 (σ i)) := by
    refine ⟨by fun_prop, ?_⟩
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    apply Subtype.ext
    exact Real.sq_sqrt (σ i).coe_nonneg
  have hpi := measurePreserving_pi (fun _ => gaussianReal 0 1)
    (fun i => gaussianReal 0 (σ i)) hscale
  have hsum := measurePreserving_sumPiEquivProdPi (fun i => gaussianReal 0 (σ i))
  have htwo := (measurePreserving_piFinTwo (fun i => gaussianReal 0 (σ (.inl i)))).prod
    (measurePreserving_piFinTwo (fun i => gaussianReal 0 (σ (.inr i))))
  exact (htwo.comp (hsum.comp hpi)).map_eq

/-- Coefficients of `X+cY±D` and `Y±E` on the four standard coordinates. -/
noncomputable def twoVertexForms (s v r : ℝ≥0) (c : ℝ) :
    Fin 4 → (Fin 2 ⊕ Fin 2) → ℝ :=
  ![Sum.elim ![Real.sqrt s, c * Real.sqrt v] ![Real.sqrt r, 0],
    Sum.elim ![Real.sqrt s, c * Real.sqrt v] ![-Real.sqrt r, 0],
    Sum.elim ![0, Real.sqrt v] ![0, Real.sqrt r],
    Sum.elim ![0, Real.sqrt v] ![0, -Real.sqrt r]]

theorem form_twoVertexForms (s v r : ℝ≥0) (c : ℝ)
    (ω : (Fin 2 ⊕ Fin 2) → ℝ) (i : Fin 4) :
    form (twoVertexForms s v r c i) ω =
      ![(patchSample s v r ω).1.1 + c * (patchSample s v r ω).1.2 +
          (patchSample s v r ω).2.1,
        (patchSample s v r ω).1.1 + c * (patchSample s v r ω).1.2 -
          (patchSample s v r ω).2.1,
        (patchSample s v r ω).1.2 + (patchSample s v r ω).2.2,
        (patchSample s v r ω).1.2 - (patchSample s v r ω).2.2] i := by
  fin_cases i <;>
    simp [form, twoVertexForms, patchSample, Fintype.sum_sum_type, Fin.sum_univ_two] <;> ring

/-- Unit variances of the four ports when both centers have variance `v` and
the center and difference variances add to one. -/
theorem sum_twoVertexForms_sq (s v r : ℝ≥0) (c : ℝ)
    (hcenter : (s : ℝ) + c ^ 2 * v = v) (hunit : (v : ℝ) + r = 1) (i : Fin 4) :
    ∑ j, twoVertexForms s v r c i j ^ 2 = 1 := by
  fin_cases i <;>
    simp [twoVertexForms, Fintype.sum_sum_type, Fin.sum_univ_two, mul_pow,
      Real.sq_sqrt s.coe_nonneg, Real.sq_sqrt v.coe_nonneg,
      Real.sq_sqrt r.coe_nonneg] <;> linarith

/-- The two within-side correlations and the four cross-side correlations. -/
theorem inner_twoVertexForms (s v r : ℝ≥0) (c : ℝ)
    (hcenter : (s : ℝ) + c ^ 2 * v = v) (i j : Fin 4) (hij : i < j) :
    ∑ k, twoVertexForms s v r c i k * twoVertexForms s v r c j k =
      if (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) then (v : ℝ) - r else c * v := by
  have hprod : c * Real.sqrt (v : ℝ) * Real.sqrt v = c * v := by
    rw [mul_assoc, Real.mul_self_sqrt v.coe_nonneg]
  fin_cases i <;> fin_cases j <;> try norm_num at hij
  all_goals
    simp [twoVertexForms, Fintype.sum_sum_type, Fin.sum_univ_two,
      ← sq, mul_pow, Real.sq_sqrt s.coe_nonneg, Real.sq_sqrt v.coe_nonneg,
      Real.sq_sqrt r.coe_nonneg]
  all_goals
    nlinarith [Real.sq_sqrt s.coe_nonneg, Real.sq_sqrt v.coe_nonneg,
      Real.sq_sqrt r.coe_nonneg]

/-- The simultaneous-straddle estimate, now for four explicit unit-coordinate forms. -/
theorem gaussPi_twoVertexForms_double_straddle_le (s v r : ℝ≥0)
    (hs : s ≠ 0) (hv : v ≠ 0) (hr : r ≠ 0) (c t : ℝ) :
    (gaussPi (Fin 2 ⊕ Fin 2)).real
      {ω | Between t (form (twoVertexForms s v r c 0) ω) (form (twoVertexForms s v r c 1) ω) ∧
        Between t (form (twoVertexForms s v r c 2) ω) (form (twoVertexForms s v r c 3) ω)} ≤
      4 * r / (Real.pi ^ 2 * Real.sqrt ((s : ℝ) * v)) := by
  let A : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {p |
    Between t (p.1.1 + c * p.1.2 + p.2.1) (p.1.1 + c * p.1.2 - p.2.1) ∧
      Between t (p.1.2 + p.2.2) (p.1.2 - p.2.2)}
  have hA : MeasurableSet A := by
    unfold A Between
    measurability
  have heq : {ω | Between t (form (twoVertexForms s v r c 0) ω)
      (form (twoVertexForms s v r c 1) ω) ∧
      Between t (form (twoVertexForms s v r c 2) ω)
        (form (twoVertexForms s v r c 3) ω)} = patchSample s v r ⁻¹' A := by
    ext ω
    simp [form_twoVertexForms, A]
  rw [heq, ← map_measureReal_apply (by unfold patchSample; fun_prop) hA,
    gaussPi_map_patchSample]
  exact prod_gaussianReal_double_straddle_le s v r hs hv hr c t

/-- Optimal cut cost for the explicit four Gaussian outer ports. -/
noncomputable def twoVertexGaussianCost (s v r : ℝ≥0) (c t : ℝ)
    (ω : (Fin 2 ⊕ Fin 2) → ℝ) : ℝ :=
  twoVertexCost
    (belowThreshold t (form (twoVertexForms s v r c 0) ω))
    (belowThreshold t (form (twoVertexForms s v r c 1) ω))
    (belowThreshold t (form (twoVertexForms s v r c 2) ω))
    (belowThreshold t (form (twoVertexForms s v r c 3) ω))

/-- A uniform expected-cost bound for the symmetric two-vertex Gaussian model.
The two within-side correlations are `v-r`, and every cross-side correlation is `cv`.
The independent-difference term is essential in this bound. -/
theorem integral_twoVertexGaussianCost_le (s v r : ℝ≥0)
    (hs : s ≠ 0) (hv : v ≠ 0) (hr : r ≠ 0) (c t : ℝ)
    (hcenter : (s : ℝ) + c ^ 2 * v = v) (hunit : (v : ℝ) + r = 1)
    (hwithin : -1 < (v : ℝ) - r) (hcross : -1 < c * v) :
    (∫ ω, twoVertexGaussianCost s v r c t ω ∂gaussPi (Fin 2 ⊕ Fin 2)) ≤
      Real.arccos ((v : ℝ) - r) / Real.pi + Real.arccos (c * v) / Real.pi +
        2 * r / (Real.pi ^ 2 * Real.sqrt ((s : ℝ) * v)) := by
  have hp (i j : Fin 4) (hij : i < j) :
      (gaussPi (Fin 2 ⊕ Fin 2)).real
        {ω | Between t (form (twoVertexForms s v r c i) ω)
          (form (twoVertexForms s v r c j) ω)} ≤
        if (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) then Real.arccos ((v : ℝ) - r) / Real.pi
          else Real.arccos (c * v) / Real.pi := by
    have hρ : -1 < ∑ k, twoVertexForms s v r c i k * twoVertexForms s v r c j k := by
      rw [inner_twoVertexForms s v r c hcenter i j hij]
      split_ifs <;> assumption
    have h := gaussPi_between_le_arccos
      (sum_twoVertexForms_sq s v r c hcenter hunit i)
      (sum_twoVertexForms_sq s v r c hcenter hunit j) hρ t
    rw [inner_twoVertexForms s v r c hcenter i j hij] at h
    split_ifs at h ⊢ <;> exact h
  have h₀₁ := hp 0 1 (by decide)
  have h₂₃ := hp 2 3 (by decide)
  have h₀₂ := hp 0 2 (by decide)
  have h₀₃ := hp 0 3 (by decide)
  have h₁₂ := hp 1 2 (by decide)
  have h₁₃ := hp 1 3 (by decide)
  norm_num only [Fin.isValue, Fin.reduceEq, and_true, true_and, true_or, ite_true, false_and,
    or_false, ite_false, false_or] at h₀₁ h₂₃ h₀₂ h₀₃ h₁₂ h₁₃
  have hd := gaussPi_twoVertexForms_double_straddle_le s v r hs hv hr c t
  rw [show 4 * (r : ℝ) / (Real.pi ^ 2 * Real.sqrt ((s : ℝ) * v)) =
    2 * (2 * r / (Real.pi ^ 2 * Real.sqrt ((s : ℝ) * v))) by ring] at hd
  have hmeas (i : Fin 4) :
      Measurable (fun ω => belowThreshold t (form (twoVertexForms s v r c i) ω)) :=
    (measurable_belowThreshold t).comp (measurable_form _)
  unfold twoVertexGaussianCost
  rw [integral_twoVertexCost _ _ _ _ _ (hmeas 0) (hmeas 1) (hmeas 2) (hmeas 3)]
  simp only [belowThreshold_ne_iff]
  linarith only [h₀₁, h₂₃, h₀₂, h₀₃, h₁₂, h₁₃, hd]

/-- The local two-vertex coefficient for within-side correlation `(1+2√2)/4`
and cross-side correlation `(2+√2)/4`. It is approximately `0.2770916915`.
This definition is not a universal graph-layout coefficient. -/
noncomputable def twoVertexTreeBound : ℝ :=
  Real.arccos ((1 + 2 * Real.sqrt 2) / 4) / Real.pi +
    Real.arccos ((2 + Real.sqrt 2) / 4) / Real.pi +
      2 * (3 - 2 * Real.sqrt 2) / (Real.pi ^ 2 * (1 + 2 * Real.sqrt 2))

/-- An explicit symmetric Gaussian model attains the stated local upper bound
at every threshold. Its covariance data is included in the conclusion. -/
theorem exists_twoVertexTreeModel :
    ∃ (s v r : ℝ≥0) (c : ℝ),
      (∀ i, ∑ k, twoVertexForms s v r c i k ^ 2 = 1) ∧
      (∀ i j : Fin 4, i < j →
        ∑ k, twoVertexForms s v r c i k * twoVertexForms s v r c j k =
          if (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) then (1 + 2 * Real.sqrt 2) / 4
            else (2 + Real.sqrt 2) / 4) ∧
      ∀ t, (∫ ω, twoVertexGaussianCost s v r c t ω ∂gaussPi (Fin 2 ⊕ Fin 2)) ≤
        twoVertexTreeBound := by
  have hu : Real.sqrt 2 < 3 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hu2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  let v : ℝ≥0 := .mk ((5 + 2 * Real.sqrt 2) / 8) (by positivity)
  let r : ℝ≥0 := .mk ((3 - 2 * Real.sqrt 2) / 8) (by linarith)
  have hv : 0 < (v : ℝ) := by simp only [v, NNReal.coe_mk]; positivity
  have hr : 0 < (r : ℝ) := by simp only [r, NNReal.coe_mk]; linarith
  let s : ℝ≥0 := .mk (((1 + 2 * Real.sqrt 2) / 8) ^ 2 / v) (by positivity)
  let c : ℝ := ((2 + Real.sqrt 2) / 4) / v
  have hs : 0 < (s : ℝ) := by simp only [s, NNReal.coe_mk]; positivity
  have hcenter : (s : ℝ) + c ^ 2 * v = v := by
    simp only [s, c, v, NNReal.coe_mk]
    field_simp
    nlinarith [hu2]
  have hunit : (v : ℝ) + r = 1 := by simp only [v, r, NNReal.coe_mk]; ring
  have hw : (v : ℝ) - r = (1 + 2 * Real.sqrt 2) / 4 := by
    simp only [v, r, NNReal.coe_mk]; ring
  have hc : c * v = (2 + Real.sqrt 2) / 4 := by dsimp [c]; field_simp
  have hdet : Real.sqrt ((s : ℝ) * v) = (1 + 2 * Real.sqrt 2) / 8 := by
    simp only [s, NNReal.coe_mk]
    rw [div_mul_cancel₀ _ hv.ne', Real.sqrt_sq (by positivity)]
  have hterm : 2 * (r : ℝ) / (Real.pi ^ 2 * Real.sqrt ((s : ℝ) * v)) =
      2 * (3 - 2 * Real.sqrt 2) / (Real.pi ^ 2 * (1 + 2 * Real.sqrt 2)) := by
    rw [hdet]
    simp only [r, NNReal.coe_mk]
    field_simp
  refine ⟨s, v, r, c, sum_twoVertexForms_sq s v r c hcenter hunit, ?_, ?_⟩
  · intro i j hij
    rw [inner_twoVertexForms s v r c hcenter i j hij, hw, hc]
  · intro t
    have h := integral_twoVertexGaussianCost_le s v r
      (by exact_mod_cast hs.ne') (by exact_mod_cast hv.ne') (by exact_mod_cast hr.ne') c t
      hcenter hunit (by rw [hw]; linarith [Real.sqrt_nonneg 2])
        (by rw [hc]; linarith [Real.sqrt_nonneg 2])
    simpa only [hw, hc, hterm, twoVertexTreeBound] using h

/-- The local estimate applies to any Gaussian forms with the tree-model Gram
matrix, regardless of their ambient dimension or choice of coordinates. -/
theorem integral_twoVertexCost_le_of_tree_gram {ι : Type} [Fintype ι]
    (a : Fin 4 → ι → ℝ) (hunit : ∀ i, ∑ k, a i k ^ 2 = 1)
    (hpair : ∀ i j : Fin 4, i < j → ∑ k, a i k * a j k =
      if (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) then (1 + 2 * Real.sqrt 2) / 4
        else (2 + Real.sqrt 2) / 4) (t : ℝ) :
    (∫ ω, (twoVertexCost
      (belowThreshold t (form (a 0) ω)) (belowThreshold t (form (a 1) ω))
      (belowThreshold t (form (a 2) ω)) (belowThreshold t (form (a 3) ω)) : ℝ)
        ∂gaussPi ι) ≤ twoVertexTreeBound := by
  obtain ⟨s, v, r, c, hu, hp, hcost⟩ := exists_twoVertexTreeModel
  have hgram (i j : Fin 4) : ∑ k, a i k * a j k =
      ∑ k, twoVertexForms s v r c i k * twoVertexForms s v r c j k := by
    rcases lt_trichotomy i j with h | rfl | h
    · rw [hpair i j h, hp i j h]
    · simp only [← sq, hunit, hu]
    · simpa only [mul_comm] using (hpair j i h).trans (hp j i h).symm
  have hlaw := gaussPi_map_forms_eq_of_gram a (twoVertexForms s v r c) hgram
  let f : (Fin 4 → ℝ) → ℝ := fun z => twoVertexCost
    (belowThreshold t (z 0)) (belowThreshold t (z 1))
    (belowThreshold t (z 2)) (belowThreshold t (z 3))
  have hf : Measurable f := by
    have hfinite : Measurable (fun z : Fin 4 → Bool =>
        (twoVertexCost (z 0) (z 1) (z 2) (z 3) : ℝ)) := measurable_of_countable _
    have hcolors : Measurable (fun z : Fin 4 → ℝ => fun i => belowThreshold t (z i)) :=
      Measurable.of_eval fun i =>
        (measurable_belowThreshold t).comp (measurable_pi_apply i)
    simpa only [Function.comp_def, f] using hfinite.comp hcolors
  have ha : Measurable (fun ω i => form (a i) ω) := by unfold form; fun_prop
  have hb : Measurable (fun ω i => form (twoVertexForms s v r c i) ω) := by
    unfold form
    fun_prop
  have heq : (∫ ω, f (fun i => form (a i) ω) ∂gaussPi ι) =
      ∫ ω, f (fun i => form (twoVertexForms s v r c i) ω) ∂gaussPi (Fin 2 ⊕ Fin 2) := by
    rw [← integral_map ha.aemeasurable hf.aestronglyMeasurable, hlaw,
      integral_map hb.aemeasurable hf.aestronglyMeasurable]
  exact heq.trans_le (hcost t)

/-- A rational certificate for the local coefficient, with comfortable slack. -/
theorem twoVertexTreeBound_le : twoVertexTreeBound ≤ 5559 / 20000 := by
  have hlo : (14142 : ℝ) / 10000 < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hpi := Real.pi_gt_d4
  have hpi' := Real.pi_lt_d4
  have hwithin : Real.arccos ((1 + 2 * Real.sqrt 2) / 4) / Real.pi ≤ 3 / 32 := by
    have h := two_mul_gaussianCoefficient_le
    unfold gaussianCoefficient at h
    rw [div_le_iff₀ Real.pi_pos]
    field_simp at h
    linarith
  have hcross : Real.arccos ((2 + Real.sqrt 2) / 4) / Real.pi ≤ 1751 / 10000 := by
    let θ := 1751 * Real.pi / 10000
    have hθ0 : 0 ≤ θ := by dsimp [θ]; positivity
    have hθ1 : θ ≤ 1 := by dsimp [θ]; linarith
    have hθlo : 0.55007 ≤ θ := by dsimp [θ]; linarith
    have hθhi : θ ≤ 0.55010 := by dsimp [θ]; linarith
    have hcos : Real.cos θ ≤ (2 + Real.sqrt 2) / 4 := by
      have hb := Real.cos_bound (x := θ) (by rw [abs_of_nonneg hθ0]; exact hθ1)
      rw [abs_of_nonneg hθ0] at hb
      have h₂ : 0.55007 ^ 2 ≤ θ ^ 2 := by gcongr
      have h₄ : θ ^ 4 ≤ 0.55010 ^ 4 := by gcongr
      nlinarith [(abs_sub_le_iff.mp hb).1]
    have ha := (Real.arccos_le_arccos hcos).trans_eq
      (Real.arccos_cos hθ0 (by dsimp [θ]; linarith [Real.pi_pos]))
    rw [div_le_iff₀ Real.pi_pos]
    dsimp [θ] at ha
    linarith
  have hterm : 2 * (3 - 2 * Real.sqrt 2) /
      (Real.pi ^ 2 * (1 + 2 * Real.sqrt 2)) ≤ 91 / 10000 := by
    rw [div_le_iff₀ (by positivity)]
    have hp₂ : (3.1415 : ℝ) ^ 2 ≤ Real.pi ^ 2 := by nlinarith
    have hd : 3.1415 ^ 2 * (1 + 2 * 1.4142) ≤
        Real.pi ^ 2 * (1 + 2 * Real.sqrt 2) := by gcongr; linarith
    nlinarith
  unfold twoVertexTreeBound
  linarith

/-- A rational lower certificate for twice the original Gaussian coefficient. -/
theorem two_mul_gaussianCoefficient_ge : 279 / 1000 ≤ 2 * gaussianCoefficient := by
  have hhi : Real.sqrt 2 < (141422 : ℝ) / 100000 :=
    (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hθ : 93 * Real.pi / 1000 ≤ Real.arccos ((1 + 2 * Real.sqrt 2) / 4) := by
    have hcos : (1 + 2 * Real.sqrt 2) / 4 ≤ Real.cos (93 * Real.pi / 1000) := by
      have h := Real.one_sub_sq_div_two_le_cos (x := 93 * Real.pi / 1000)
      have hsq : (93 * Real.pi / 1000) ^ 2 ≤ (0.29217 : ℝ) ^ 2 := by
        gcongr
        linarith [Real.pi_lt_d4]
      nlinarith
    exact (Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])).symm.trans_le
      (Real.arccos_le_arccos hcos)
  unfold gaussianCoefficient
  have heq : 2 * (3 / (2 * Real.pi) * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) =
      3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4) / Real.pi := by field_simp
  rw [heq, le_div_iff₀ Real.pi_pos]
  linarith

/-- The local symmetric two-vertex bound is strictly below twice the existing
one-vertex Gaussian coefficient. No finite-graph transfer is asserted here. -/
theorem twoVertexTreeBound_lt_two_mul_gaussianCoefficient :
    twoVertexTreeBound < 2 * gaussianCoefficient := by
  linarith [twoVertexTreeBound_le, two_mul_gaussianCoefficient_ge]

end Frontier.Gaussian
