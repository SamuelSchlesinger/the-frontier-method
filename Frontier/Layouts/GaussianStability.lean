/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.GaussianPatch
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Stability of the Gaussian pair estimate

Covariance square roots couple nearby Gaussian laws in a fixed coordinate
space. Sheppard's threshold bound controls the probability that corresponding
ports acquire different colors, uniformly over the threshold. Since the
optimized pair cost changes by at most one per changed port, its expectation
is uniformly stable under small covariance errors.
-/

@[expose] public section

namespace Frontier.Gaussian

open MeasureTheory ProbabilityTheory Set

/-- Changing outer port colors costs at most one per changed port. -/
theorem twoVertexCost_le_add_disagreements (a b : Fin 4 → Bool) :
    twoVertexCost (a 0) (a 1) (a 2) (a 3) ≤
      twoVertexCost (b 0) (b 1) (b 2) (b 3) + ∑ i, portDisagreement (a i) (b i) := by
  revert a b
  decide

/-- The optimized pair cost for four real scores at a common threshold. -/
noncomputable def twoVertexThresholdCost (t : ℝ) (z : Fin 4 → ℝ) : ℝ :=
  twoVertexCost (belowThreshold t (z 0)) (belowThreshold t (z 1))
    (belowThreshold t (z 2)) (belowThreshold t (z 3))

theorem measurable_twoVertexThresholdCost (t : ℝ) : Measurable (twoVertexThresholdCost t) := by
  unfold twoVertexThresholdCost
  have hf : Measurable (fun a : Fin 4 → Bool =>
      (twoVertexCost (a 0) (a 1) (a 2) (a 3) : ℝ)) := measurable_of_countable _
  have hc : Measurable (fun z : Fin 4 → ℝ => fun i => belowThreshold t (z i)) :=
    Measurable.of_eval fun i =>
      (measurable_belowThreshold t).comp (measurable_pi_apply i)
  simpa only [Function.comp_def, twoVertexThresholdCost] using hf.comp hc

private theorem twoVertexCost_le_two (a b c d : Bool) : twoVertexCost a b c d ≤ 2 := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem integrable_twoVertexThresholdCost {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (z : Ω → Fin 4 → ℝ)
    (hz : Measurable z) (t : ℝ) : Integrable (fun ω => twoVertexThresholdCost t (z ω)) μ := by
  refine Integrable.of_bound
    ((measurable_twoVertexThresholdCost t).comp hz).aestronglyMeasurable 2 ?_
  exact ae_of_all _ fun ω => by
    simpa only [twoVertexThresholdCost, Real.norm_natCast, Nat.cast_le_ofNat] using
      twoVertexCost_le_two (belowThreshold t (z ω 0)) (belowThreshold t (z ω 1))
        (belowThreshold t (z ω 2)) (belowThreshold t (z ω 3))

/-- A coupling of four unit forms with correlation at least `ρ > -1`
changes the expected optimized pair cost by at most `4 arccos ρ / π`.
The estimate holds at every threshold. -/
theorem integral_twoVertexThresholdCost_le_of_correlation {ι : Type} [Fintype ι]
    (a b : Fin 4 → ι → ℝ) (ha : ∀ i, ∑ k, a i k ^ 2 = 1)
    (hb : ∀ i, ∑ k, b i k ^ 2 = 1) {ρ : ℝ} (hρ : -1 < ρ)
    (hab : ∀ i, ρ ≤ ∑ k, a i k * b i k) (t : ℝ) :
    (∫ ω, twoVertexThresholdCost t (fun i => form (a i) ω) ∂gaussPi ι) ≤
      (∫ ω, twoVertexThresholdCost t (fun i => form (b i) ω) ∂gaussPi ι) +
        4 * Real.arccos ρ / Real.pi := by
  classical
  let E (i : Fin 4) := {ω | belowThreshold t (form (a i) ω) ≠
    belowThreshold t (form (b i) ω)}
  let I (i : Fin 4) : (ι → ℝ) → ℝ := (E i).indicator (fun _ => 1)
  have hE (i) : MeasurableSet (E i) := (measurableSet_eq_fun
    ((measurable_belowThreshold t).comp (measurable_form (a i)))
    ((measurable_belowThreshold t).comp (measurable_form (b i)))).compl
  have hI (i) : Integrable (I i) (gaussPi ι) := (integrable_const 1).indicator (hE i)
  have hpoint (ω : ι → ℝ) :
      twoVertexThresholdCost t (fun i => form (a i) ω) ≤
        twoVertexThresholdCost t (fun i => form (b i) ω) + ∑ i, I i ω := by
    have h := twoVertexCost_le_add_disagreements
      (fun i => belowThreshold t (form (a i) ω))
      (fun i => belowThreshold t (form (b i) ω))
    have hi (i) : (portDisagreement (belowThreshold t (form (a i) ω))
        (belowThreshold t (form (b i) ω)) : ℝ) = I i ω := by
      simp only [portDisagreement, I, E, Set.indicator, mem_ofPred_eq]
      split_ifs <;> simp_all
    simpa only [Nat.cast_add, Nat.cast_sum, hi, twoVertexThresholdCost] using
      (Nat.cast_le (α := ℝ)).mpr h
  have hma : Measurable (fun ω i => form (a i) ω) := by unfold form; fun_prop
  have hmb : Measurable (fun ω i => form (b i) ω) := by unfold form; fun_prop
  have h := integral_mono (integrable_twoVertexThresholdCost _ _ hma t)
    ((integrable_twoVertexThresholdCost _ _ hmb t).add (integrable_finsetSum _ fun i _ => hI i))
    hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (integrable_twoVertexThresholdCost _ _ hmb t)
    (integrable_finsetSum Finset.univ fun i _ => hI i),
    integral_finsetSum _ fun i _ => hI i] at h
  refine h.trans (add_le_add_right ?_ _)
  have hi (i) : (∫ ω, I i ω ∂gaussPi ι) ≤ Real.arccos ρ / Real.pi := by
    have hp := gaussPi_between_le_arccos (ha i) (hb i) (hρ.trans_le (hab i)) t
    have he : (∫ ω, I i ω ∂gaussPi ι) = (gaussPi ι).real (E i) := by
      simp only [I, integral_indicator_const (1 : ℝ) (hE i), smul_eq_mul, mul_one]
    rw [he]
    simp only [E, belowThreshold_ne_iff]
    exact hp.trans (div_le_div_of_nonneg_right (Real.arccos_le_arccos (hab i)) Real.pi_pos.le)
  calc
    ∑ i, (∫ ω, I i ω ∂gaussPi ι) ≤ ∑ _ : Fin 4, Real.arccos ρ / Real.pi :=
      Finset.sum_le_sum fun i _ => hi i
    _ = 4 * Real.arccos ρ / Real.pi := by simp; ring

open scoped MatrixOrder

open Classical in
/-- The rows of the positive square root realize a positive semidefinite Gram matrix. -/
theorem sqrt_gram {κ : Type} [Fintype κ]
    (A : Matrix κ κ ℝ) (hA : A.PosSemidef) (i j : κ) :
    ∑ k, CFC.sqrt A i k * CFC.sqrt A j k = A i j := by
  classical
  have hh := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hsym (k) : CFC.sqrt A k j = CFC.sqrt A j k := by simpa using hh.apply j k
  have he := congrFun (congrFun (CFC.sqrt_mul_sqrt_self A hA.nonneg) i) j
  simpa only [Matrix.mul_apply, hsym] using he

open scoped Matrix.Norms.L2Operator in
open Classical in
private theorem continuousOn_sqrt_matrix {κ : Type} [Fintype κ] :
    ContinuousOn (CFC.sqrt : Matrix κ κ ℝ → _) {A | A.PosSemidef} := by
  classical
  simpa only [Matrix.nonneg_iff_posSemidef] using
    (CFC.continuousOn_sqrt (A := Matrix κ κ ℝ))

open scoped Matrix.Norms.Elementwise in
open Classical in
private theorem exists_sqrt_correlation_tolerance {κ : Type} [Fintype κ]
    (B : Matrix κ κ ℝ) (hB : B.PosSemidef) (hdiag : ∀ i, B i i = 1)
    (ρ : ℝ) (hρ : ρ < 1) :
    ∃ δ > 0, ∀ A : Matrix κ κ ℝ, A.PosSemidef →
      (∀ i j, |A i j - B i j| < δ) →
      ∀ i, ρ < ∑ k, CFC.sqrt A i k * CFC.sqrt B i k := by
  classical
  have hc (i : κ) : ContinuousWithinAt
      (fun A : Matrix κ κ ℝ => ∑ k, CFC.sqrt A i k * CFC.sqrt B i k)
      {A | A.PosSemidef} B := by
    have hlin : Continuous (fun M : Matrix κ κ ℝ => ∑ k, M i k * CFC.sqrt B i k) := by
      fun_prop
    exact hlin.continuousAt.comp_continuousWithinAt (continuousOn_sqrt_matrix B hB)
  have he (i) : (∑ k, CFC.sqrt B i k * CFC.sqrt B i k) = 1 := by
    rw [sqrt_gram B hB, hdiag]
  have hn : {A : Matrix κ κ ℝ | ∀ i, ρ < ∑ k, CFC.sqrt A i k * CFC.sqrt B i k}
      ∈ nhdsWithin B {A | A.PosSemidef} := by
    exact Filter.eventually_all.mpr fun i =>
      (hc i).eventually (isOpen_Ioi.mem_nhds (by simpa only [mem_Ioi, he] using hρ))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp hn
  refine ⟨δ, hδ, fun A hA hclose => hball ⟨?_, hA⟩⟩
  exact (dist_pi_lt_iff hδ).mpr fun i =>
    (dist_pi_lt_iff hδ).mpr fun j => by simpa only [Real.dist_eq] using hclose i j

/-- The expected threshold cost depends only on the Gram matrix of the four
score vectors, including when the two realizations have different dimensions. -/
theorem integral_twoVertexThresholdCost_eq_of_gram {ι ν : Type} [Fintype ι] [Fintype ν]
    (a : Fin 4 → ι → ℝ) (b : Fin 4 → ν → ℝ)
    (h : ∀ i j, ∑ k, a i k * a j k = ∑ k, b i k * b j k) (t : ℝ) :
    (∫ ω, twoVertexThresholdCost t (fun i => form (a i) ω) ∂gaussPi ι) =
      ∫ ω, twoVertexThresholdCost t (fun i => form (b i) ω) ∂gaussPi ν := by
  have ha : Measurable (fun ω i => form (a i) ω) := by unfold form; fun_prop
  have hb : Measurable (fun ω i => form (b i) ω) := by unfold form; fun_prop
  rw [← integral_map ha.aemeasurable (measurable_twoVertexThresholdCost t).aestronglyMeasurable,
    gaussPi_map_forms_eq_of_gram a b h,
    integral_map hb.aemeasurable (measurable_twoVertexThresholdCost t).aestronglyMeasurable]

open scoped Topology in
/-- Small covariance errors preserve an upper bound on the expected optimized
pair cost at any fixed unit-variance model. The tolerance is independent of
both the threshold and the ambient dimension of the perturbed realization. -/
theorem exists_twoVertexThresholdCost_tolerance {ν : Type} [Fintype ν]
    (b : Fin 4 → ν → ℝ) (hb : ∀ i, ∑ k, b i k ^ 2 = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {ι : Type} [Fintype ι] (a : Fin 4 → ι → ℝ),
      (∀ i, ∑ k, a i k ^ 2 = 1) →
      (∀ i j, |(∑ k, a i k * a j k) - (∑ k, b i k * b j k)| < δ) →
      ∀ t, (∫ ω, twoVertexThresholdCost t (fun i => form (a i) ω) ∂gaussPi ι) ≤
        (∫ ω, twoVertexThresholdCost t (fun i => form (b i) ω) ∂gaussPi ν) + ε := by
  classical
  have hc : Continuous (fun ρ : ℝ => 4 * Real.arccos ρ / Real.pi) := by fun_prop
  have hlo : ∀ᶠ ρ in 𝓝 (1 : ℝ), -1 < ρ := Ioi_mem_nhds (by norm_num)
  have he : ∀ᶠ ρ in 𝓝 (1 : ℝ), -1 < ρ ∧ 4 * Real.arccos ρ / Real.pi < ε :=
    hlo.and
      (hc.continuousAt.eventually (Iio_mem_nhds (by simpa using hε)))
  obtain ⟨ρ, ⟨hρlo, hρcost⟩, hρhi⟩ :=
    ((he.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : ∀ᶠ ρ in 𝓝[<] (1 : ℝ), ρ < 1)).exists
  let B : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of b * Matrix.conjTranspose b
  have hB : B.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose b
  have hBij (i j) : B i j = ∑ k, b i k * b j k := rfl
  have hBdiag (i) : B i i = 1 := by simpa only [hBij, ← sq] using hb i
  obtain ⟨δ, hδ, hnear⟩ := exists_sqrt_correlation_tolerance B hB hBdiag ρ hρhi
  refine ⟨δ, hδ, fun {ι} _ a ha hgram t => ?_⟩
  let A : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of a * Matrix.conjTranspose a
  have hA : A.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose a
  have hAij (i j) : A i j = ∑ k, a i k * a j k := rfl
  have hAdiag (i) : A i i = 1 := by simpa only [hAij, ← sq] using ha i
  have hcoup (i) : ρ ≤ ∑ k, CFC.sqrt A i k * CFC.sqrt B i k :=
    (hnear A hA (by simpa only [hAij, hBij] using hgram) i).le
  have hua (i) : ∑ k, CFC.sqrt A i k ^ 2 = 1 := by
    simpa only [sq] using (sqrt_gram A hA i i).trans (hAdiag i)
  have hub (i) : ∑ k, CFC.sqrt B i k ^ 2 = 1 := by
    simpa only [sq] using (sqrt_gram B hB i i).trans (hBdiag i)
  let a' : Matrix (Fin 4) (Fin 4) ℝ := CFC.sqrt A
  let b' : Matrix (Fin 4) (Fin 4) ℝ := CFC.sqrt B
  rw [integral_twoVertexThresholdCost_eq_of_gram a a'
    (fun i j => (hAij i j).symm.trans (sqrt_gram A hA i j).symm) t,
    integral_twoVertexThresholdCost_eq_of_gram b b'
      (fun i j => (hBij i j).symm.trans (sqrt_gram B hB i j).symm) t]
  exact (integral_twoVertexThresholdCost_le_of_correlation
    a' b' hua hub hρlo hcoup t).trans (add_le_add_right hρcost.le _)

/-- The symmetric tree-model estimate survives sufficiently small errors in
its six correlations, uniformly over all thresholds and finite realizations. -/
theorem exists_twoVertexTree_tolerance {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {ι : Type} [Fintype ι] (a : Fin 4 → ι → ℝ),
      (∀ i, ∑ k, a i k ^ 2 = 1) →
      (∀ i j : Fin 4, i < j →
        |(∑ k, a i k * a j k) -
          (if (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) then (1 + 2 * Real.sqrt 2) / 4
            else (2 + Real.sqrt 2) / 4)| < δ) →
      ∀ t, (∫ ω, twoVertexThresholdCost t (fun i => form (a i) ω) ∂gaussPi ι) ≤
        twoVertexTreeBound + ε := by
  obtain ⟨s, v, r, c, hu, hp, hcost⟩ := exists_twoVertexTreeModel
  obtain ⟨δ, hδ, hnear⟩ := exists_twoVertexThresholdCost_tolerance
    (twoVertexForms s v r c) hu hε
  refine ⟨δ, hδ, fun {ι} _ a ha hpair t => ?_⟩
  have hgram (i j : Fin 4) : |(∑ k, a i k * a j k) -
      (∑ k, twoVertexForms s v r c i k * twoVertexForms s v r c j k)| < δ := by
    rcases lt_trichotomy i j with h | rfl | h
    · simpa only [hp i j h] using hpair i j h
    · simpa only [← sq, ha, hu, sub_self, abs_zero] using hδ
    · have hh := hpair j i h
      rw [← hp j i h] at hh
      simpa only [mul_comm] using hh
  refine (hnear a ha hgram t).trans ?_
  simpa only [twoVertexThresholdCost, twoVertexGaussianCost] using
    add_le_add (hcost t) (le_refl ε)

/-- A positive part of the tree-model improvement survives covariance errors.
This supplies a robust local saving; assembling patches into a concentrated
complete ordering is a separate obligation. -/
theorem exists_twoVertexTree_saving :
    ∃ δ > 0, ∃ η > 0, ∀ {ι : Type} [Fintype ι] (a : Fin 4 → ι → ℝ),
      (∀ i, ∑ k, a i k ^ 2 = 1) →
      (∀ i j : Fin 4, i < j →
        |(∑ k, a i k * a j k) -
          (if (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) then (1 + 2 * Real.sqrt 2) / 4
            else (2 + Real.sqrt 2) / 4)| < δ) →
      ∀ t, (∫ ω, twoVertexThresholdCost t (fun i => form (a i) ω) ∂gaussPi ι) + η ≤
        2 * gaussianCoefficient := by
  let η := (2 * gaussianCoefficient - twoVertexTreeBound) / 2
  have hη : 0 < η := by
    dsimp [η]
    linarith only [twoVertexTreeBound_lt_two_mul_gaussianCoefficient]
  obtain ⟨δ, hδ, hnear⟩ := exists_twoVertexTree_tolerance hη
  refine ⟨δ, hδ, η, hη, fun {ι} _ a ha hpair t => ?_⟩
  have h := hnear a ha hpair t
  dsimp [η] at h ⊢
  linarith only [h]

end Frontier.Gaussian
