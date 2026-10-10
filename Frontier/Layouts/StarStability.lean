/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.Gaussian
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Stability of the three-vector star inequality

For unit edge vectors `y₀,y₁,y₂` having inner product at least `κ` with a unit
center `x`, define the gap as `‖y₀+y₁+y₂‖²-9κ²`. It is nonnegative and controls
both the excess center correlations and the residual of the three-vector sum.
When the edge vectors are normalized sums with their neighboring vertex rows,
the same gap controls the neighboring star residual used in `KernelCovariance`.

Thus a near-extremizer of the star inequality has small *measured* residuals;
they need not be assumed independently. Turning a large gap into a uniform
probability saving, and combining patches globally, are separate steps.
-/

@[expose] public section

namespace Frontier.Gaussian

open Finset

variable {ι : Type*} [Fintype ι]

/-- Slack in the squared-norm proof of the three-vector star inequality. -/
def starGap (κ : ℝ) (y : Fin 3 → ι → ℝ) : ℝ :=
  (∑ k, (∑ j, y j k) ^ 2) - 9 * κ ^ 2

/-- For unit rows, the gap is twice the excess sum of the three edge correlations. -/
theorem starGap_eq_pairs (κ : ℝ) (y : Fin 3 → ι → ℝ)
    (hy : ∀ j, ∑ k, y j k ^ 2 = 1) :
    starGap κ y = 3 + 2 * ((∑ k, y 0 k * y 1 k) +
      (∑ k, y 0 k * y 2 k) + ∑ k, y 1 k * y 2 k) - 9 * κ ^ 2 := by
  have heq (k : ι) : (∑ j, y j k) ^ 2 =
      y 0 k ^ 2 + y 1 k ^ 2 + y 2 k ^ 2 +
        2 * (y 0 k * y 1 k + y 0 k * y 2 k + y 1 k * y 2 k) := by
    norm_num [Fin.sum_univ_succ]
    ring
  simp only [starGap, heq, sum_add_distrib, ← mul_sum, hy]
  ring

private theorem sum_star_inner (x : ι → ℝ) (y : Fin 3 → ι → ℝ) :
    (∑ k, (∑ j, y j k) * x k) = ∑ j, ∑ k, y j k * x k := by
  simp only [sum_mul]
  exact sum_comm

/-- The Cauchy gap controls the total excess of the center correlations. -/
theorem star_inner_excess_le (x : ι → ℝ) (y : Fin 3 → ι → ℝ) {κ : ℝ}
    (hx : ∑ k, x k ^ 2 = 1) :
    6 * κ * (∑ j, ((∑ k, y j k * x k) - κ)) ≤ starGap κ y := by
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun k => ∑ j, y j k) x
  rw [hx, mul_one, sum_star_inner] at hcs
  have he : (∑ j, ((∑ k, y j k * x k) - κ)) =
      (∑ j, ∑ k, y j k * x k) - 3 * κ := by
    simp [sum_sub_distrib]
  rw [he]
  unfold starGap
  nlinarith only [hcs, sq_nonneg ((∑ j, ∑ k, y j k * x k) - 3 * κ)]

/-- A star satisfying the correlation lower bounds has nonnegative gap. -/
theorem starGap_nonneg (x : ι → ℝ) (y : Fin 3 → ι → ℝ) {κ : ℝ}
    (hx : ∑ k, x k ^ 2 = 1) (hκ : 0 ≤ κ)
    (hinner : ∀ j, κ ≤ ∑ k, y j k * x k) : 0 ≤ starGap κ y := by
  have h := star_inner_excess_le x y (κ := κ) hx
  have he : 0 ≤ ∑ j, ((∑ k, y j k * x k) - κ) :=
    sum_nonneg fun j _ => sub_nonneg.mpr (hinner j)
  exact (mul_nonneg (by positivity) he).trans h

/-- The sum of the edge vectors is close to its extremal multiple of the center. -/
theorem sum_star_residual_sq_le (x : ι → ℝ) (y : Fin 3 → ι → ℝ) {κ : ℝ}
    (hx : ∑ k, x k ^ 2 = 1) (hκ : 0 ≤ κ)
    (hinner : ∀ j, κ ≤ ∑ k, y j k * x k) :
    (∑ k, ((∑ j, y j k) - 3 * κ * x k) ^ 2) ≤ starGap κ y := by
  have heq : (∑ k, ((∑ j, y j k) - 3 * κ * x k) ^ 2) =
      (∑ k, (∑ j, y j k) ^ 2) - 6 * κ * (∑ j, ∑ k, y j k * x k) +
        9 * κ ^ 2 := by
    calc
      _ = (∑ k, (∑ j, y j k) ^ 2) -
          6 * κ * (∑ k, (∑ j, y j k) * x k) + 9 * κ ^ 2 * (∑ k, x k ^ 2) := by
        simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
        apply sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [hx, mul_one, sum_star_inner]
  have hlo : 3 * κ ≤ ∑ j, ∑ k, y j k * x k := by
    simpa using (sum_le_sum fun j (_ : j ∈ (univ : Finset (Fin 3))) => hinner j)
  rw [heq]
  unfold starGap
  nlinarith [mul_nonneg hκ (sub_nonneg.mpr hlo)]

private theorem star_inner_le_one (x z : ι → ℝ)
    (hx : ∑ k, x k ^ 2 = 1) (hz : ∑ k, z k ^ 2 = 1) :
    ∑ k, z k * x k ≤ 1 := by
  have h := sum_mul_sq_le_sq_mul_sq univ z x
  rw [hx, hz] at h
  nlinarith

/-- With `κ≥1/2`, three times the total nonnegative correlation excess is at most the gap. -/
theorem three_mul_star_excess_le (x : ι → ℝ) (y : Fin 3 → ι → ℝ) {κ : ℝ}
    (hx : ∑ k, x k ^ 2 = 1) (hκ : 1 / 2 ≤ κ)
    (hinner : ∀ j, κ ≤ ∑ k, y j k * x k) :
    3 * (∑ j, ((∑ k, y j k * x k) - κ)) ≤ starGap κ y := by
  have h := star_inner_excess_le x y (κ := κ) hx
  have he : 0 ≤ ∑ j, ((∑ k, y j k * x k) - κ) :=
    sum_nonneg fun j _ => sub_nonneg.mpr (hinner j)
  nlinarith

/-- When the normalized edge vector is `y`, the other endpoint is
`2⟨y,x⟩y-x`. Its center correlation has only a small excess when the star gap is small. -/
theorem reconstructed_inner_excess_le (x : ι → ℝ) (y : Fin 3 → ι → ℝ) {κ : ℝ}
    (hx : ∑ k, x k ^ 2 = 1) (hy : ∀ j, ∑ k, y j k ^ 2 = 1)
    (hκ : 1 / 2 ≤ κ) (hκ1 : κ ≤ 1)
    (hinner : ∀ j, κ ≤ ∑ k, y j k * x k) (j : Fin 3) :
    3 * (2 * (∑ k, y j k * x k) ^ 2 - 1 - (2 * κ ^ 2 - 1)) ≤
      4 * starGap κ y := by
  have hsum := three_mul_star_excess_le x y hx hκ hinner
  have hone := star_inner_le_one x (y j) hx (hy j)
  have hle := single_le_sum
    (fun i (_ : i ∈ (univ : Finset (Fin 3))) => sub_nonneg.mpr (hinner i)) (mem_univ j)
  have hnonneg := hinner j
  nlinarith [mul_nonneg (sub_nonneg.mpr hnonneg)
    (show 0 ≤ 2 - ((∑ k, y j k * x k) + κ) by linarith)]

/-- A small star gap controls the neighboring vertex residual, not just the edge rows.
The bound is independent of the number of Gaussian coordinates. -/
theorem sum_reconstructedStar_sq_le (x : ι → ℝ) (y : Fin 3 → ι → ℝ) {κ : ℝ}
    (hx : ∑ k, x k ^ 2 = 1) (hy : ∀ j, ∑ k, y j k ^ 2 = 1)
    (hκ : 1 / 2 ≤ κ) (hκ1 : κ ≤ 1)
    (hinner : ∀ j, κ ≤ ∑ k, y j k * x k) :
    (∑ k, ((∑ j, (2 * (∑ l, y j l * x l) * y j k - x k)) -
      3 * (2 * κ ^ 2 - 1) * x k) ^ 2) ≤ 16 * starGap κ y := by
  let a (j : Fin 3) := (∑ k, y j k * x k) - κ
  have ha (j : Fin 3) : 0 ≤ a j := sub_nonneg.mpr (hinner j)
  have ha1 (j : Fin 3) : a j ≤ 1 := by
    have h := star_inner_le_one x (y j) hx (hy j)
    dsimp [a]
    linarith
  have hasq : (∑ j, a j ^ 2) ≤ ∑ j, a j := by
    apply sum_le_sum
    intro j _
    nlinarith [ha j, ha1 j]
  have hexcess := three_mul_star_excess_le x y hx hκ hinner
  change 3 * (∑ j, a j) ≤ starGap κ y at hexcess
  have hweighted : (∑ k, (∑ j, a j * y j k) ^ 2) ≤ starGap κ y := by
    calc
      _ ≤ ∑ k, (∑ j, a j ^ 2) * ∑ j, y j k ^ 2 :=
        sum_le_sum fun k _ => sum_mul_sq_le_sq_mul_sq univ a (fun j => y j k)
      _ = 3 * ∑ j, a j ^ 2 := by
        rw [← mul_sum, sum_comm]
        simp [hy, mul_comm]
      _ ≤ 3 * ∑ j, a j := mul_le_mul_of_nonneg_left hasq (by norm_num)
      _ ≤ starGap κ y := hexcess
  have hres := sum_star_residual_sq_le x y hx (by linarith : 0 ≤ κ) hinner
  have hgap := starGap_nonneg x y hx (by linarith : 0 ≤ κ) hinner
  have heq (k : ι) : (∑ j, (2 * (∑ l, y j l * x l) * y j k - x k)) -
      3 * (2 * κ ^ 2 - 1) * x k =
      2 * κ * ((∑ j, y j k) - 3 * κ * x k) + 2 * (∑ j, a j * y j k) := by
    simp only [a, Fin.sum_univ_succ]
    ring
  have hsplit := sum_le_sum (s := univ) (fun k (_ : k ∈ (univ : Finset ι)) =>
    show (2 * κ * ((∑ j, y j k) - 3 * κ * x k) + 2 * (∑ j, a j * y j k)) ^ 2 ≤
      8 * κ ^ 2 * ((∑ j, y j k) - 3 * κ * x k) ^ 2 +
        8 * (∑ j, a j * y j k) ^ 2 by
      nlinarith [sq_nonneg (κ * ((∑ j, y j k) - 3 * κ * x k) -
        (∑ j, a j * y j k))])
  simp only [heq]
  refine hsplit.trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hκsq : κ ^ 2 ≤ 1 := by nlinarith
  have hrnonneg : 0 ≤ ∑ k, ((∑ j, y j k) - 3 * κ * x k) ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  nlinarith [mul_nonneg (sub_nonneg.mpr hκsq) hrnonneg]

section Kernel

variable {W : Type} [Fintype W] (H : SimpleGraph W)

/-- The other kernel row is recovered exactly from the normalized edge row and one endpoint. -/
theorem edgeVector_reconstruct {q : ℝ} {R : ℕ} {u v : W}
    (hpos : 0 < pairNormSq H q R u v) (k : W) :
    2 * (∑ z, edgeVector H q R s(u, v) z * unitKernel H q R v z) *
      edgeVector H q R s(u, v) k - unitKernel H q R v k = unitKernel H q R u k := by
  have hs : Real.sqrt (pairNormSq H q R u v) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hnum : (∑ z, (unitKernel H q R u z + unitKernel H q R v z) *
      unitKernel H q R v z) = 1 + ∑ z, unitKernel H q R u z * unitKernel H q R v z := by
    simp only [add_mul, sum_add_distrib, ← pow_two, sum_unitKernel_sq]
    ring
  have hnorm : Real.sqrt (pairNormSq H q R u v) ^ 2 =
      2 + 2 * ∑ z, unitKernel H q R u z * unitKernel H q R v z :=
    (Real.sq_sqrt hpos.le).trans (pairNormSq_eq H q R u v)
  simp only [edgeVector_mk, div_mul_eq_mul_div, ← sum_div, hnum]
  field_simp
  linear_combination -(unitKernel H q R u k + unitKernel H q R v k) * hnorm

/-- The squared endpoint correlation of a normalized sum gives the original row correlation. -/
theorem edgeVector_correlation {q : ℝ} {R : ℕ} {u v : W}
    (hpos : 0 < pairNormSq H q R u v) :
    2 * (∑ z, edgeVector H q R s(u, v) z * unitKernel H q R v z) ^ 2 - 1 =
      ∑ z, unitKernel H q R u z * unitKernel H q R v z := by
  rw [sum_edgeVector_mul hpos]
  have hp : 0 ≤ (1 + ∑ z, unitKernel H q R u z * unitKernel H q R v z) / 2 := by
    rw [pairNormSq_eq] at hpos
    linarith
  rw [Real.sq_sqrt hp]
  ring

/-- Actual finite kernel rows inherit the correlation-excess estimate from their edge star. -/
theorem unitKernel_correlation_le_starGap (v : W) (u : Fin 3 → W) {q κ : ℝ} {R : ℕ}
    (hpos : ∀ j, 0 < pairNormSq H q R (u j) v)
    (hκ : 1 / 2 ≤ κ) (hκ1 : κ ≤ 1)
    (hinner : ∀ j, κ ≤ ∑ z, edgeVector H q R s(u j, v) z * unitKernel H q R v z)
    (j : Fin 3) :
    (∑ z, unitKernel H q R (u j) z * unitKernel H q R v z) ≤
      2 * κ ^ 2 - 1 + 4 / 3 * starGap κ (fun j => edgeVector H q R s(u j, v)) := by
  have h := reconstructed_inner_excess_le (unitKernel H q R v)
    (fun j => edgeVector H q R s(u j, v)) (sum_unitKernel_sq H q R v)
    (fun j => sum_edgeVector_sq (hpos j)) hκ hκ1 hinner j
  rw [edgeVector_correlation H (hpos j)] at h
  linarith

/-- Small edge-star gap bounds the actual neighboring-row residual on a finite graph. -/
theorem unitKernel_star_residual_le (v : W) (u : Fin 3 → W) {q κ : ℝ} {R : ℕ}
    (hpos : ∀ j, 0 < pairNormSq H q R (u j) v)
    (hκ : 1 / 2 ≤ κ) (hκ1 : κ ≤ 1)
    (hinner : ∀ j, κ ≤ ∑ z, edgeVector H q R s(u j, v) z * unitKernel H q R v z) :
    (∑ k, ((∑ j, unitKernel H q R (u j) k) -
      3 * (2 * κ ^ 2 - 1) * unitKernel H q R v k) ^ 2) ≤
        16 * starGap κ (fun j => edgeVector H q R s(u j, v)) := by
  have h := sum_reconstructedStar_sq_le (unitKernel H q R v)
    (fun j => edgeVector H q R s(u j, v)) (sum_unitKernel_sq H q R v)
    (fun j => sum_edgeVector_sq (hpos j)) hκ hκ1 hinner
  simpa only [edgeVector_reconstruct H (hpos _)] using h

/-- Moving the target eigenvalue to its critical value costs only its squared discrepancy. -/
theorem unitKernel_critical_star_residual_le (v : W) (u : Fin 3 → W) {q κ : ℝ} {R : ℕ}
    (hpos : ∀ j, 0 < pairNormSq H q R (u j) v)
    (hκ : 1 / 2 ≤ κ) (hκ1 : κ ≤ 1)
    (hinner : ∀ j, κ ≤ ∑ z, edgeVector H q R s(u j, v) z * unitKernel H q R v z) :
    (∑ k, ((∑ j, unitKernel H q R (u j) k) -
      2 * Real.sqrt 2 * unitKernel H q R v k) ^ 2) ≤
        32 * starGap κ (fun j => edgeVector H q R s(u j, v)) +
          2 * (3 * (2 * κ ^ 2 - 1) - 2 * Real.sqrt 2) ^ 2 := by
  have h := unitKernel_star_residual_le H v u hpos hκ hκ1 hinner
  have hp := sum_le_sum (s := univ) (fun k (_ : k ∈ (univ : Finset W)) =>
    show ((∑ j, unitKernel H q R (u j) k) - 2 * Real.sqrt 2 * unitKernel H q R v k) ^ 2 ≤
      2 * ((∑ j, unitKernel H q R (u j) k) -
        3 * (2 * κ ^ 2 - 1) * unitKernel H q R v k) ^ 2 +
      2 * (3 * (2 * κ ^ 2 - 1) - 2 * Real.sqrt 2) ^ 2 * unitKernel H q R v k ^ 2 by
        nlinarith [sq_nonneg (((∑ j, unitKernel H q R (u j) k) -
          3 * (2 * κ ^ 2 - 1) * unitKernel H q R v k) -
            (3 * (2 * κ ^ 2 - 1) - 2 * Real.sqrt 2) * unitKernel H q R v k)])
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_unitKernel_sq, mul_one] at hp
  linarith

end Kernel

end Frontier.Gaussian
