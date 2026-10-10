/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.Kernel
import Mathlib.Algebra.BigOperators.Field

/-!
# Ratio stability of finite distance kernels

A nearly sharp adjacent-row correlation forces small total error from the two
distance ratios. This accounts for unequal row normalizers, equal-distance
coordinates, and truncation. The estimates apply to the actual finite kernel.
-/

@[expose] public section

namespace Frontier.Gaussian

open Finset

private theorem normalization_error_le {q A B C Z ε δ : ℝ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hq : 1 / 2 ≤ q) (hq₁ : q ≤ 1)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1 / 4)
    (hc : 2 * q / (1 + q ^ 2) * (A ^ 2 + B ^ 2) / 2 - δ ≤ C)
    (htop : C ≤ A * B) (hupp : C ≤ (2 * q / (1 + q ^ 2) + ε) * (A * B))
    (hZ : Z ≤ (1 + q ^ 2) * C - q * (A ^ 2 + B ^ 2) + 4 * δ) :
    2 * (Z / A ^ 2) + 2 * (B / A - 1) ^ 2 ≤ 48 * ε + 16 * δ := by
  have hA₀ : 0 < A := by linarith
  have hB₀ : 0 < B := by linarith
  have hA₂ : 1 ≤ A ^ 2 := by nlinarith
  have hq₀ : 0 ≤ q := by linarith
  have hq₂ : q ^ 2 ≤ 1 := by nlinarith [mul_nonneg hq₀ (sub_nonneg.mpr hq₁)]
  let κ := 2 * q / (1 + q ^ 2)
  change κ * (A ^ 2 + B ^ 2) / 2 - δ ≤ C at hc
  change C ≤ (κ + ε) * (A * B) at hupp
  have hκ : 1 / 2 ≤ κ := by
    dsimp [κ]
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hκeq : (1 + q ^ 2) * κ = 2 * q := by dsimp [κ]; field_simp
  have hhalf := mul_le_mul_of_nonneg_right hκ (add_nonneg (sq_nonneg A) (sq_nonneg B))
  have hquad : B ^ 2 ≤ 4 * (A * B) := by nlinarith
  have hBA : B ≤ 4 * A := by
    by_contra h
    have hmul := mul_lt_mul_of_pos_right (lt_of_not_ge h) hB₀
    nlinarith
  have hE : ε * (A * B) ≤ 4 * ε * A ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hBA (mul_nonneg hε hA₀.le)]
  have hδA : δ ≤ δ * A ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hA₂ hδ]
  have hgap : (B - A) ^ 2 ≤ (16 * ε + 4 * δ) * A ^ 2 := by
    have hhalfGap := mul_le_mul_of_nonneg_right hκ (sq_nonneg (B - A))
    nlinarith
  have hgap' : (B / A - 1) ^ 2 ≤ 16 * ε + 4 * δ := by
    have heq : (B / A - 1) ^ 2 = (B - A) ^ 2 / A ^ 2 := by field_simp
    rw [heq, div_le_iff₀ (sq_pos_of_pos hA₀)]
    exact hgap
  have hsum := mul_le_mul_of_nonneg_left
    (show 2 * (A * B) ≤ A ^ 2 + B ^ 2 by nlinarith [sq_nonneg (B - A)]) hq₀
  have hlift := mul_le_mul_of_nonneg_left hupp (show 0 ≤ 1 + q ^ 2 by positivity)
  have hbaseline : (1 + q ^ 2) * (κ * (A * B)) = 2 * q * (A * B) := by
    rw [← mul_assoc, hκeq]
  have hweight : (1 + q ^ 2) * (ε * (A * B)) ≤ 2 * (ε * (A * B)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hZ' : Z / A ^ 2 ≤ 8 * ε + 4 * δ := by
    rw [div_le_iff₀ (sq_pos_of_pos hA₀)]
    nlinarith only [hZ, hlift, hbaseline, hsum, hweight, hE, hδA]
  linarith

/-- The effect of changing two row normalizers on the total ratio error. -/
theorem sum_edgeRatioError_div_le {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) {q A B : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1)
    (hA : A ≠ 0) (hB : B ≠ 0) (hb : ∑ k, (b k / B) ^ 2 = 1) :
    (∑ k, edgeRatioError q (a k / A) (b k / B)) ≤
      2 * ((∑ k, edgeRatioError q (a k) (b k)) / A ^ 2) + 2 * (B / A - 1) ^ 2 := by
  have h := sum_le_sum fun k (_ : k ∈ univ) => edgeRatioError_div_le hq₀ hq₁ hA hB (a k) (b k)
  simpa only [sum_add_distrib, ← mul_sum, ← sum_div, hb, mul_one, mul_div_assoc] using h

/-- Ratio perturbation for unit rows has a dimension-independent cost. -/
theorem sum_edgeRatioError_ratio_le_of_unit {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (ha : ∑ k, a k ^ 2 = 1) (hb : ∑ k, b k ^ 2 = 1) (p q : ℝ) :
    (∑ k, edgeRatioError p (a k) (b k)) ≤
      2 * (∑ k, edgeRatioError q (a k) (b k)) + 4 * (p - q) ^ 2 := by
  have h := sum_le_sum fun k (_ : k ∈ univ) => edgeRatioError_ratio_le p q (a k) (b k)
  simp only [sum_add_distrib, ← mul_sum, ha, hb] at h
  nlinarith only [h]

section Finite

variable {W : Type} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- Nearly sharp adjacent correlation controls the ratio error of the actual
finite normalized kernel. No girth or equal-normalizer hypothesis is used. -/
theorem sum_unitKernel_edgeRatioError_le {D : ℕ} (hD : 2 ≤ D)
    (degree : ∀ v, H.degree v ≤ D) {q ε : ℝ} (hq : 1 / 2 ≤ q) (hq₁ : q ≤ 1)
    (hε : 0 ≤ ε) (R : ℕ) {u v : W} (huv : H.Adj u v)
    (htail : (D : ℝ) * ((D - 1 : ℕ) * q ^ 2) ^ R ≤ 1 / 4)
    (hcorr : (∑ z, unitKernel H q R u z * unitKernel H q R v z) ≤
      2 * q / (1 + q ^ 2) + ε) :
    (∑ z, edgeRatioError q (unitKernel H q R u z) (unitKernel H q R v z)) ≤
      48 * ε + 16 * D * ((D - 1 : ℕ) * q ^ 2) ^ R := by
  have hq₀ : 0 ≤ q := by linarith
  let A := Real.sqrt (∑ z, kernel H q R u z ^ 2)
  let B := Real.sqrt (∑ z, kernel H q R v z ^ 2)
  let C := ∑ z, kernel H q R u z * kernel H q R v z
  have hA : 1 ≤ A := Real.one_le_sqrt.mpr (one_le_sum_kernel_sq H R u)
  have hB : 1 ≤ B := Real.one_le_sqrt.mpr (one_le_sum_kernel_sq H R v)
  have hA₀ : 0 < A := by linarith
  have hB₀ : 0 < B := by linarith
  have hAA : A ^ 2 = ∑ z, kernel H q R u z ^ 2 := by
    dsimp [A]
    exact Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
  have hBB : B ^ 2 = ∑ z, kernel H q R v z ^ 2 := by
    dsimp [B]
    exact Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
  have hlower : 2 * q / (1 + q ^ 2) * (A ^ 2 + B ^ 2) / 2 -
      D * ((D - 1 : ℕ) * q ^ 2) ^ R ≤ C := by
    rw [hAA, hBB]
    exact sum_kernel_mul_ge_degree H hD degree q R huv
  have htop : C ≤ A * B := by
    exact Real.sum_mul_le_sqrt_mul_sqrt univ (kernel H q R u) (kernel H q R v)
  have hupp : C ≤ (2 * q / (1 + q ^ 2) + ε) * (A * B) := by
    simp only [unitKernel, div_mul_div_comm, ← sum_div] at hcorr
    change C / (A * B) ≤ 2 * q / (1 + q ^ 2) + ε at hcorr
    exact (div_le_iff₀ (mul_pos hA₀ hB₀)).mp hcorr
  have hraw := sum_kernel_edgeRatioError_le H hD degree hq₀ hq₁ R huv
  rw [← hAA, ← hBB] at hraw
  have hnorm := sum_edgeRatioError_div_le (kernel H q R u) (kernel H q R v)
    hq₀ hq₁ hA₀.ne' hB₀.ne' (sum_unitKernel_sq H q R v)
  refine hnorm.trans ?_
  have h := normalization_error_le hA hB hq hq₁ hε (by positivity) htail hlower htop hupp
    (by simpa only [mul_assoc] using hraw)
  simpa only [mul_assoc] using h

/-- In particular the same finite rows approach the critical cubic ratio as
their correlation slack, truncation error, and ratio perturbation vanish. -/
theorem sum_unitKernel_criticalRatioError_le {D : ℕ} (hD : 2 ≤ D)
    (degree : ∀ v, H.degree v ≤ D) {q ε : ℝ} (hq : 1 / 2 ≤ q) (hq₁ : q ≤ 1)
    (hε : 0 ≤ ε) (R : ℕ) {u v : W} (huv : H.Adj u v)
    (htail : (D : ℝ) * ((D - 1 : ℕ) * q ^ 2) ^ R ≤ 1 / 4)
    (hcorr : (∑ z, unitKernel H q R u z * unitKernel H q R v z) ≤
      2 * q / (1 + q ^ 2) + ε) :
    (∑ z, edgeRatioError (Real.sqrt 2 / 2) (unitKernel H q R u z) (unitKernel H q R v z)) ≤
      96 * ε + 32 * D * ((D - 1 : ℕ) * q ^ 2) ^ R + 4 * (Real.sqrt 2 / 2 - q) ^ 2 := by
  have h := sum_edgeRatioError_ratio_le_of_unit (unitKernel H q R u) (unitKernel H q R v)
    (sum_unitKernel_sq H q R u) (sum_unitKernel_sq H q R v) (Real.sqrt 2 / 2) q
  have hqerr := sum_unitKernel_edgeRatioError_le H hD degree hq hq₁ hε R huv htail hcorr
  linarith

end Finite

end Frontier.Gaussian
