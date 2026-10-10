/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.GaussianStability
import Mathlib.Analysis.Matrix.Order

/-!
# Explicit covariance stability for Gaussian pairs

A positive semidefinite residual `A - c² B` couples the law with covariance
`A` to a copy of the reference law with covariance `B`, with coordinatewise
correlation `c`. This supplies numerical tolerances without a qualitative
continuity argument for the matrix square root.
-/

@[expose] public section

namespace Frontier.Gaussian

open Finset MeasureTheory Matrix
open scoped MatrixOrder

/-- Entrywise covariance error bounds the error of every quadratic form. -/
theorem quadraticForm_error_le {κ : Type*} [Fintype κ]
    (A B : Matrix κ κ ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hAB : ∀ i j, |A i j - B i j| ≤ δ) (x : κ → ℝ) :
    |x ⬝ᵥ ((A - B) *ᵥ x)| ≤ δ * Fintype.card κ * ∑ i, x i ^ 2 := by
  have hterm (i j : κ) : |x i * (A i j - B i j) * x j| ≤
      δ * ((x i ^ 2 + x j ^ 2) / 2) := by
    calc
      _ = |A i j - B i j| * (|x i| * |x j|) := by rw [abs_mul, abs_mul]; ring
      _ ≤ δ * (|x i| * |x j|) := mul_le_mul_of_nonneg_right (hAB i j) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by
        nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]) hδ
  have he : x ⬝ᵥ ((A - B) *ᵥ x) = ∑ i, ∑ j, x i * (A i j - B i j) * x j := by
    simp only [dotProduct, Matrix.mulVec, Matrix.sub_apply, mul_sum]
    congr 1
    funext i
    apply sum_congr rfl
    intro j _
    ring
  rw [he]
  calc
    _ ≤ ∑ i, |∑ j, x i * (A i j - B i j) * x j| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |x i * (A i j - B i j) * x j| :=
      sum_le_sum fun _ _ => abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, δ * ((x i ^ 2 + x j ^ 2) / 2) :=
      sum_le_sum fun i _ => sum_le_sum fun j _ => hterm i j
    _ = _ := by
      simp_rw [add_div, mul_add, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul,
        ← mul_sum, ← sum_div]
      ring

/-- A spectral lower bound for the reference covariance converts entrywise
errors into a positive residual suitable for an explicit Gaussian coupling. -/
theorem residual_posSemidef {κ : Type*} [Fintype κ]
    (A B : Matrix κ κ ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    {δ ℓ c : ℝ} (hδ : 0 ≤ δ) (hc : c ^ 2 ≤ 1)
    (hAB : ∀ i j, |A i j - B i j| ≤ δ)
    (hBlower : ∀ x : κ → ℝ, ℓ * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (B *ᵥ x))
    (hsmall : δ * Fintype.card κ ≤ (1 - c ^ 2) * ℓ) :
    (A - c ^ 2 • B).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hA.sub (hB.smul (show IsSelfAdjoint (c ^ 2) from .of_nonneg (sq_nonneg c))))
  intro x
  have he := quadraticForm_error_le A B hδ hAB x
  have hb := mul_le_mul_of_nonneg_left (hBlower x) (sub_nonneg.mpr hc)
  have hs := mul_le_mul_of_nonneg_right hsmall
    (show 0 ≤ ∑ i, x i ^ 2 from sum_nonneg fun i _ => sq_nonneg (x i))
  have hid : x ⬝ᵥ ((A - c ^ 2 • B) *ᵥ x) =
      x ⬝ᵥ ((A - B) *ᵥ x) + (1 - c ^ 2) * (x ⬝ᵥ (B *ᵥ x)) := by
    simp [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]
    ring
  simp only [star_trivial]
  rw [hid]
  linarith [neg_abs_le (x ⬝ᵥ ((A - B) *ᵥ x))]

/-- A positive residual gives a coupling with correlation exactly `c` in
each coordinate, uniformly over the threshold and the realization dimension. -/
theorem integral_twoVertexThresholdCost_le_of_residual
    {ι ν : Type} [Fintype ι] [Fintype ν]
    (a : Fin 4 → ι → ℝ) (b : Fin 4 → ν → ℝ)
    (ha : ∀ i, ∑ k, a i k ^ 2 = 1) (hb : ∀ i, ∑ k, b i k ^ 2 = 1)
    {c : ℝ} (hc : -1 < c)
    (hR : ((Matrix.of a * Matrix.conjTranspose a) -
      c ^ 2 • (Matrix.of b * Matrix.conjTranspose b)).PosSemidef) (t : ℝ) :
    (∫ ω, twoVertexThresholdCost t (fun i => form (a i) ω) ∂gaussPi ι) ≤
      (∫ ω, twoVertexThresholdCost t (fun i => form (b i) ω) ∂gaussPi ν) +
        4 * Real.arccos c / Real.pi := by
  classical
  let R := (Matrix.of a * Matrix.conjTranspose a) -
    c ^ 2 • (Matrix.of b * Matrix.conjTranspose b)
  let a' (i : Fin 4) : ν ⊕ Fin 4 → ℝ :=
    Sum.elim (fun k => c * b i k) (fun k => CFC.sqrt R i k)
  let b' (i : Fin 4) : ν ⊕ Fin 4 → ℝ := Sum.elim (b i) (fun _ => 0)
  have hga (i j) : ∑ k, a' i k * a' j k = ∑ k, a i k * a j k := by
    simp only [a', Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, sqrt_gram R hR]
    have hmul : (∑ k, c * b i k * (c * b j k)) = c ^ 2 * ∑ k, b i k * b j k := by
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      ring
    rw [hmul]
    change c ^ 2 * (∑ k, b i k * b j k) +
      ((∑ k, a i k * a j k) - c ^ 2 * (∑ k, b i k * b j k)) = _
    ring
  have hgb (i j) : ∑ k, b' i k * b' j k = ∑ k, b i k * b j k := by simp [b']
  have hua (i) : ∑ k, a' i k ^ 2 = 1 := by
    simpa only [sq] using (hga i i).trans (by simpa [sq] using ha i)
  have hub (i) : ∑ k, b' i k ^ 2 = 1 := by
    simpa only [sq] using (hgb i i).trans (by simpa [sq] using hb i)
  have hcouple (i) : c ≤ ∑ k, a' i k * b' i k := by
    simp only [a', b', Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, mul_zero,
      sum_const_zero, add_zero, mul_assoc, ← mul_sum, ← sq, hb, mul_one, le_refl]
  rw [integral_twoVertexThresholdCost_eq_of_gram a a' (fun i j => (hga i j).symm) t,
    integral_twoVertexThresholdCost_eq_of_gram b b' (fun i j => (hgb i j).symm) t]
  exact integral_twoVertexThresholdCost_le_of_correlation a' b' hua hub hc hcouple t

/-- The four-port covariance matrix of the symmetric tree model. -/
noncomputable def treePortGram : Matrix (Fin 4) (Fin 4) ℝ := fun i j =>
  if i = j then 1 else if i.val / 2 = j.val / 2 then (1 + 2 * Real.sqrt 2) / 4
    else (2 + Real.sqrt 2) / 4

@[simp] theorem treePortGram_diag (i : Fin 4) : treePortGram i i = 1 := by simp [treePortGram]

theorem treePortGram_symm (i j : Fin 4) : treePortGram i j = treePortGram j i := by
  simp only [treePortGram, eq_comm]

theorem treePortGram_of_lt (i j : Fin 4) (hij : i < j) :
    treePortGram i j = if (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) then
      (1 + 2 * Real.sqrt 2) / 4 else (2 + Real.sqrt 2) / 4 := by
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals norm_num [treePortGram]

/-- A rational spectral lower bound for the reference matrix. -/
theorem treePortGram_quadratic_lower (x : Fin 4 → ℝ) :
    (1 / 25 : ℝ) * (∑ i, x i ^ 2) ≤ x ⬝ᵥ (treePortGram *ᵥ x) := by
  let a := (1 + 2 * Real.sqrt 2) / 4
  let b := (2 + Real.sqrt 2) / 4
  have hid : x ⬝ᵥ (treePortGram *ᵥ x) = (1 - a) * (∑ i, x i ^ 2) +
      (a - b) * ((x 0 + x 1) ^ 2 + (x 2 + x 3) ^ 2) +
        b * (x 0 + x 1 + x 2 + x 3) ^ 2 := by
    simp [treePortGram, a, b, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
    ring
  have hlo : 1 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hhi : Real.sqrt 2 ≤ 71 / 50 :=
    (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have hcoeff : 1 / 25 ≤ 1 - a := by dsimp [a]; linarith
  have hab : 0 ≤ a - b := by dsimp [a, b]; linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  rw [hid]
  have h := mul_le_mul_of_nonneg_right hcoeff
    (show 0 ≤ ∑ i, x i ^ 2 from sum_nonneg fun _ _ => sq_nonneg _)
  linarith [mul_nonneg hab (add_nonneg (sq_nonneg (x 0 + x 1)) (sq_nonneg (x 2 + x 3))),
    mul_nonneg hb (sq_nonneg (x 0 + x 1 + x 2 + x 3))]

private theorem explicit_coupling_error :
    4 * Real.arccos (1 - 1 / 10 ^ 10) / Real.pi ≤ 1 / 5000 := by
  have hcos : Real.cos (1 / 10000 : ℝ) ≤ 1 - 1 / 10 ^ 10 := by
    have h := Real.cos_bound (x := (1 / 10000 : ℝ)) (by norm_num)
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 10000)] at h
    nlinarith [(abs_sub_le_iff.mp h).1]
  have hangle := (Real.arccos_le_arccos hcos).trans_eq
    (Real.arccos_cos (by norm_num) (by linarith [Real.two_le_pi]))
  rw [div_le_iff₀ Real.pi_pos]
  nlinarith [Real.two_le_pi]

/-- An entrywise error of `10⁻¹⁴` costs at most `1/5000` in the local
expected pair cost, uniformly over all thresholds and ambient dimensions. -/
theorem integral_twoVertexThresholdCost_le_tree_explicit {ι : Type} [Fintype ι]
    (a : Fin 4 → ι → ℝ) (ha : ∀ i, ∑ k, a i k ^ 2 = 1)
    (hgram : ∀ i j, |(∑ k, a i k * a j k) - treePortGram i j| ≤ 1 / 10 ^ 14)
    (t : ℝ) :
    (∫ ω, twoVertexThresholdCost t (fun i => form (a i) ω) ∂gaussPi ι) ≤
      twoVertexTreeBound + 1 / 5000 := by
  obtain ⟨s, v, r, c, hu, hp, hcost⟩ := exists_twoVertexTreeModel
  let b := twoVertexForms s v r c
  have hbgram (i j : Fin 4) : ∑ k, b i k * b j k = treePortGram i j := by
    have hupper (i j : Fin 4) (hij : i ≤ j) :
        ∑ k, b i k * b j k = treePortGram i j := by
      rcases hij.eq_or_lt with rfl | hij
      · simpa only [treePortGram_diag, ← sq] using hu i
      · rw [treePortGram_of_lt i j hij]
        exact hp i j hij
    rcases le_total i j with h | h
    · exact hupper i j h
    · simpa only [mul_comm, treePortGram_symm j i] using hupper j i h
  have hB : Matrix.of b * Matrix.conjTranspose b = treePortGram := by
    ext i j
    exact hbgram i j
  have hR : ((Matrix.of a * Matrix.conjTranspose a) -
      (1 - 1 / 10 ^ 10 : ℝ) ^ 2 • (Matrix.of b * Matrix.conjTranspose b)).PosSemidef := by
    rw [hB]
    apply residual_posSemidef _ _ (Matrix.isHermitian_mul_conjTranspose_self a)
      (show treePortGram.IsHermitian by ext i j; exact treePortGram_symm j i)
      (δ := 1 / 10 ^ 14) (ℓ := 1 / 25) (by norm_num) (by norm_num)
      hgram treePortGram_quadratic_lower
    norm_num
  have h := integral_twoVertexThresholdCost_le_of_residual a b ha hu
    (by norm_num : (-1 : ℝ) < 1 - 1 / 10 ^ 10) hR t
  have hb : (∫ ω, twoVertexThresholdCost t (fun i => form (b i) ω)
      ∂gaussPi (Fin 2 ⊕ Fin 2)) ≤ twoVertexTreeBound := by
    simpa only [b, twoVertexThresholdCost, twoVertexGaussianCost] using hcost t
  exact h.trans (add_le_add hb explicit_coupling_error)

end Frontier.Gaussian
