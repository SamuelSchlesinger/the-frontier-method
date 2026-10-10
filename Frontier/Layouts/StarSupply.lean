/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.StarStability
public import Frontier.Layouts.Packing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# A uniform probability saving from star gaps

The existing Gaussian angle bound improves when the measured edge correlations
exceed the lower bound used in the star inequality. For every threshold, a
vertex with star gap `G` saves at least `G/(4π)` in straddling probability. The
saving sums over vertices before concentration is applied.

The intrinsic finite-graph gap agrees with `starGap` after enumerating the three
incident edges. Thus the same quantity gives a probability saving when large
and the covariance control of `KernelCovariance` when small. The final dichotomy
either improves one complete ordering or supplies linearly many disjoint
small-gap pairs. `PairGeometry` and `MatchingMean` subsequently bound their
approximate optimized costs. The quarter supply coefficient remains unproved.
-/

@[expose] public section

namespace Frontier.Gaussian

open Finset MeasureTheory

variable {W : Type} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The star-inequality gap without choosing an enumeration of incident edges. -/
noncomputable def edgeStarGap (q : ℝ) (R : ℕ) (ρ : ℝ) (v : W) : ℝ := by
  classical
  exact (∑ z, (∑ e ∈ H.incidenceFinset v, edgeVector H q R e z) ^ 2) - 9 * (1 + ρ) / 2

/-- The intrinsic gap is the same one used by the local covariance estimates. -/
theorem edgeStarGap_eq_starGap (q : ℝ) (R : ℕ) (ρ κ : ℝ) (v : W)
    (ports : Fin 3 ≃ ↥(H.incidenceFinset v)) (hκ : κ ^ 2 = (1 + ρ) / 2) :
    edgeStarGap H q R ρ v = starGap κ (fun j => edgeVector H q R (ports j)) := by
  classical
  have hs (z : W) : (∑ e ∈ H.incidenceFinset v, edgeVector H q R e z) =
      ∑ j, edgeVector H q R (ports j) z := by
    rw [← sum_coe_sort]
    exact (ports.sum_comp (fun e => edgeVector H q R e z)).symm
  simp only [edgeStarGap, starGap, hs, hκ]
  ring

variable {H}

open Classical in
/-- The gap is the excess ordered-pair correlation sum. -/
theorem edgeStarGap_eq_pairs (regular : H.IsRegularOfDegree 3) {q ρ : ℝ} (hq : 0 ≤ q)
    {R : ℕ} (hρ : -1 < ρ) (hbound : ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    (v : W) : edgeStarGap H q R ρ v =
      (∑ e ∈ H.incidenceFinset v, ∑ f ∈ (H.incidenceFinset v).erase e,
        ∑ z, edgeVector H q R e z * edgeVector H q R f z) + 3 - 9 * (1 + ρ) / 2 := by
  have degree : ∀ v, H.degree v ≤ 3 := fun v => (regular.degree_eq v).le
  have h := sum_inner_ordered_pairs_eq (H.incidenceFinset v) (fun e => edgeVector H q R e)
    (fun e he => (edgeVector_star degree hq hρ hbound v he).1)
  rw [card_incidenceFinset_of_regular regular v] at h
  unfold edgeStarGap
  push_cast at h
  linarith

/-- Every finite-graph star gap is nonnegative under the existing kernel lower bound. -/
theorem edgeStarGap_nonneg (regular : H.IsRegularOfDegree 3) {q ρ : ℝ} (hq : 0 ≤ q)
    {R : ℕ} (hρ : -1 < ρ) (hbound : ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    (v : W) : 0 ≤ edgeStarGap H q R ρ v := by
  classical
  have degree : ∀ v, H.degree v ≤ 3 := fun v => (regular.degree_eq v).le
  have star := fun e (he : e ∈ H.incidenceFinset v) =>
    edgeVector_star degree hq hρ hbound v he
  have h := sum_inner_ordered_pairs_ge (sum_unitKernel_sq H q R v)
    (H.incidenceFinset v) (fun e => edgeVector H q R e)
    (fun e he => (star e he).1) (Real.sqrt_nonneg ((1 + ρ) / 2))
    (fun e he => (star e he).2)
  rw [card_incidenceFinset_of_regular regular v, Real.sq_sqrt (by linarith)] at h
  rw [edgeStarGap_eq_pairs regular hq hρ hbound v]
  push_cast at h
  linarith

/-- The measured mean correlation is at most one, including at degenerate Gaussian stars. -/
theorem edgeStarGap_le (regular : H.IsRegularOfDegree 3) {q ρ : ℝ} (hq : 0 ≤ q)
    {R : ℕ} (hρ : -1 < ρ) (hbound : ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    (v : W) : edgeStarGap H q R ρ v ≤ 9 * (1 - ρ) / 2 := by
  classical
  have degree : ∀ v, H.degree v ≤ 3 := fun v => (regular.degree_eq v).le
  have unit := fun e (he : e ∈ H.incidenceFinset v) =>
    (edgeVector_star degree hq hρ hbound v he).1
  have hone (e f : Sym2 W) (he : e ∈ H.incidenceFinset v) (hf : f ∈ H.incidenceFinset v) :
      (∑ z, edgeVector H q R e z * edgeVector H q R f z) ≤ 1 := by
    have h := sum_mul_sq_le_sq_mul_sq univ (edgeVector H q R e) (edgeVector H q R f)
    rw [unit e he, unit f hf] at h
    nlinarith
  have hsum : (∑ e ∈ H.incidenceFinset v, ∑ f ∈ (H.incidenceFinset v).erase e,
      ∑ z, edgeVector H q R e z * edgeVector H q R f z) ≤ 6 := by
    calc
      _ ≤ ∑ e ∈ H.incidenceFinset v, ∑ _f ∈ (H.incidenceFinset v).erase e, (1 : ℝ) :=
        sum_le_sum fun e he => sum_le_sum fun f hf => hone e f he (mem_of_mem_erase hf)
      _ = 6 := by
        have hc (e : Sym2 W) (he : e ∈ H.incidenceFinset v) :
            (∑ _f ∈ (H.incidenceFinset v).erase e, (1 : ℝ)) = 2 := by
          simp [card_erase_of_mem he, card_incidenceFinset_of_regular regular v]
        simp only [sum_congr rfl hc]
        norm_num [card_incidenceFinset_of_regular regular v]
  rw [edgeStarGap_eq_pairs regular hq hρ hbound v]
  linarith

/-- The inverse cosine decreases by at least the increase of its argument on `[-1,1]`.
This follows directly from the one-Lipschitz bound for cosine. -/
theorem arccos_add_difference_le {a b : ℝ} (ha : -1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Real.arccos b + (b - a) ≤ Real.arccos a := by
  have hm := Real.arccos_le_arccos hab
  have h := Real.abs_cos_sub_cos_le (Real.arccos b) (Real.arccos a)
  rw [Real.cos_arccos (ha.trans hab) hb, Real.cos_arccos ha (hab.trans hb),
    abs_of_nonneg (sub_nonneg.mpr hab), abs_of_nonpos (sub_nonpos.mpr hm)] at h
  linarith

/-- Keep all measured star slack in the uniform-threshold Gaussian bound. -/
theorem measureReal_straddleEvent_le_gap (regular : H.IsRegularOfDegree 3)
    {q ρ : ℝ} (hq : 0 ≤ q) {R : ℕ} (hρ : 17 / 32 ≤ ρ)
    (hbound : ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) (t : ℝ) (v : W) :
    (gaussPi W).real (straddleEvent H q R t v) ≤
      3 / (2 * Real.pi) * Real.arccos ((1 + 3 * ρ) / 4 + edgeStarGap H q R ρ v / 6) := by
  classical
  apply measureReal_straddleEvent_le_of_average regular hq hρ hbound
  rw [edgeStarGap_eq_pairs regular hq (by linarith) hbound v]
  linarith

/-- A positive star gap gives a definite saving at every threshold, not only at zero. -/
theorem measureReal_straddleEvent_add_gap_le (regular : H.IsRegularOfDegree 3)
    {q ρ : ℝ} (hq : 0 ≤ q) {R : ℕ} (hρ : 17 / 32 ≤ ρ)
    (hbound : ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) (t : ℝ) (v : W) :
    (gaussPi W).real (straddleEvent H q R t v) + edgeStarGap H q R ρ v / (4 * Real.pi) ≤
      straddleBound ρ := by
  have hg := edgeStarGap_nonneg regular hq (by linarith) hbound v
  have hu := edgeStarGap_le regular hq (by linarith) hbound v
  let a := (1 + 3 * ρ) / 4
  let b := a + edgeStarGap H q R ρ v / 6
  have ha : -1 ≤ a := by dsimp [a]; linarith
  have hab : a ≤ b := by dsimp [b]; linarith
  have hb : b ≤ 1 := by dsimp [b, a]; linarith
  have harc := arccos_add_difference_le ha hab hb
  calc
    _ ≤ 3 / (2 * Real.pi) * Real.arccos b + edgeStarGap H q R ρ v / (4 * Real.pi) :=
      add_le_add (measureReal_straddleEvent_le_gap regular hq hρ hbound t v) le_rfl
    _ = 3 / (2 * Real.pi) * (Real.arccos b + (b - a)) := by dsimp [b]; ring
    _ ≤ 3 / (2 * Real.pi) * Real.arccos a :=
      mul_le_mul_of_nonneg_left harc (by positivity)
    _ = straddleBound ρ := rfl

/-- Summing the same deterministic saving controls the expected straddling count uniformly
over thresholds. Concentration can be applied to this sharper mean. -/
theorem sum_measureReal_straddleEvent_add_gap_le (regular : H.IsRegularOfDegree 3)
    {q ρ : ℝ} (hq : 0 ≤ q) {R : ℕ} (hρ : 17 / 32 ≤ ρ)
    (hbound : ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R) (t : ℝ) :
    (∑ v, (gaussPi W).real (straddleEvent H q R t v)) +
      (∑ v, edgeStarGap H q R ρ v) / (4 * Real.pi) ≤ Fintype.card W * straddleBound ρ := by
  have h := sum_le_sum (s := univ) fun v (_ : v ∈ (univ : Finset W)) =>
    measureReal_straddleEvent_add_gap_le regular hq hρ hbound t v
  simpa only [sum_add_distrib, ← sum_div, sum_const, card_univ, nsmul_eq_mul] using h

/-- The summed star saving survives concentration, the threshold grid, and the conversion
to one injective ordering. The tail and window terms are exactly the existing ones. -/
theorem exists_good_sample_with_gap (regular : H.IsRegularOfDegree 3)
    {q ρ : ℝ} (hq : 0 ≤ q) (R : ℕ) (hρ : 17 / 32 ≤ ρ)
    (hbound : ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) {M : ℕ} (hM : 0 < M)
    (large : (3 * M + 3) * (vertexOverlap 3 (R + 1) : ℝ) / ε ^ 2 < Fintype.card W) :
    ∃ key : W → ℕ, Function.Injective key ∧ ∀ t : ℕ,
      (#(H.cutFinset {w | key w < t}) : ℝ) ≤ Fintype.card W *
        cubicBoundOfMean (straddleBound ρ - (∑ v, edgeStarGap H q R ρ v) /
          (4 * Real.pi * Fintype.card W)) T ε M := by
  have hh : 0 < (Fintype.card W : ℝ) := lt_of_le_of_lt (by positivity) large
  apply exists_good_sample_of_mean regular hq R hρ hbound hT hε hM large
  intro t
  have h := sum_measureReal_straddleEvent_add_gap_le regular hq hρ hbound t
  have he : (Fintype.card W : ℝ) * (straddleBound ρ - (∑ v, edgeStarGap H q R ρ v) /
      (4 * Real.pi * Fintype.card W)) = Fintype.card W * straddleBound ρ -
        (∑ v, edgeStarGap H q R ρ v) / (4 * Real.pi) := by
    field_simp
  rw [he]
  linarith

/-- A lower bound on average star gap gives a fixed reduction of the layout coefficient,
uniformly over all prefixes. This is the large-gap branch of the proposed supply dichotomy. -/
theorem exists_good_sample_of_gap_mean (regular : H.IsRegularOfDegree 3)
    {q ρ g : ℝ} (hq : 0 ≤ q) (R : ℕ) (hρ : 17 / 32 ≤ ρ)
    (hbound : ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    (hgap : Fintype.card W * g ≤ ∑ v, edgeStarGap H q R ρ v)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) {M : ℕ} (hM : 0 < M)
    (large : (3 * M + 3) * (vertexOverlap 3 (R + 1) : ℝ) / ε ^ 2 < Fintype.card W) :
    ∃ key : W → ℕ, Function.Injective key ∧ ∀ t : ℕ,
      (#(H.cutFinset {w | key w < t}) : ℝ) ≤ Fintype.card W *
        cubicBoundOfMean (straddleBound ρ - g / (4 * Real.pi)) T ε M := by
  apply exists_good_sample_of_mean regular hq R hρ hbound hT hε hM large
  intro t
  have h := sum_measureReal_straddleEvent_add_gap_le regular hq hρ hbound t
  have hg := div_le_div_of_nonneg_right hgap (by positivity : 0 ≤ 4 * Real.pi)
  rw [mul_sub, ← mul_div_assoc]
  linarith

/-- Every sufficiently large cubic graph either gains a definite amount in a common
layout, or has linearly many disjoint pairs whose endpoint star gaps are small.
`MatchingMean` estimates the optimized costs in the second alternative. -/
theorem gap_layout_or_small_gap_matching [DecidableEq W] (regular : H.IsRegularOfDegree 3)
    {q ρ τ : ℝ} (hq : 0 ≤ q) (R : ℕ) (hρ : 17 / 32 ≤ ρ) (hτ : 0 < τ)
    (hbound : ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) {M : ℕ} (hM : 0 < M)
    (large : (3 * M + 3) * (vertexOverlap 3 (R + 1) : ℝ) / ε ^ 2 < Fintype.card W) :
    (∃ key : W → ℕ, Function.Injective key ∧ ∀ t : ℕ,
      (#(H.cutFinset {w | key w < t}) : ℝ) ≤ Fintype.card W *
        cubicBoundOfMean (straddleBound ρ - τ / (24 * Real.pi)) T ε M) ∨
    (∃ pairs : Finset (Sym2 W), pairs ⊆ H.edgeFinset ∧
      (pairs : Set (Sym2 W)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset) ∧
      (∀ e ∈ pairs, ∀ v ∈ e, edgeStarGap H q R ρ v ≤ τ) ∧
        Fintype.card W ≤ 5 * pairs.card) := by
  classical
  by_cases hbig : (Fintype.card W : ℝ) * (τ / 6) ≤ ∑ v, edgeStarGap H q R ρ v
  · left
    have h := exists_good_sample_of_gap_mean regular hq R hρ hbound hbig hT hε hM large
    have he : (τ / 6) / (4 * Real.pi) = τ / (24 * Real.pi) := by ring
    simpa only [he] using h
  · right
    obtain ⟨pairs, hsub, hdisj, hgood, hsize⟩ := PairLayout.exists_matching_small_gap H regular
      (edgeStarGap H q R ρ) (edgeStarGap_nonneg regular hq (by linarith) hbound) hτ
    refine ⟨pairs, hsub, hdisj, hgood, ?_⟩
    have hsmall := (lt_of_not_ge hbig).le
    have hc : (Fintype.card W : ℝ) ≤ 5 * pairs.card := by
      by_contra! hn
      have hp := mul_pos hτ (sub_pos.mpr hn)
      nlinarith
    exact_mod_cast hc

end Frontier.Gaussian
