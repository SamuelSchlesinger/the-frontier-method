/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.KernelRigidity
public import Frontier.Layouts.StarStability

/-!
# Covariance stability with approximate critical ratios

Joint rounding of the five ratios allows the rigidity theorem to apply even
when the ratios are only approximately satisfied. The estimates below are
independent of the ambient dimension. `unitKernel_criticalStarGram_le_of_gaps`
then uses the two edge-star gaps to control both correlation errors and vertex
residuals. No Gaussian probability continuity or global layout gain is asserted
here.
-/

@[expose] public section

namespace Frontier.Gaussian

open Finset

private theorem abs_sum_mul_le {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    |∑ k, a k * b k| ≤ Real.sqrt (∑ k, a k ^ 2) * Real.sqrt (∑ k, b k ^ 2) := by
  have h : |∑ k, a k * b k| ^ 2 ≤ (∑ k, a k ^ 2) * ∑ k, b k ^ 2 := by
    simpa only [sq_abs] using sum_mul_sq_le_sq_mul_sq univ a b
  exact (Real.le_sqrt_of_sq_le h).trans_eq
    (Real.sqrt_mul (sum_nonneg fun _ _ => sq_nonneg _) _)

/-- Perturbing two unit rows by squared distance at most `δ` changes their
inner product by at most `2√δ+δ`. -/
theorem abs_sum_mul_sub_le_of_near {ι : Type*} [Fintype ι]
    (a b a' b' : ι → ℝ) {δ : ℝ} (hδ : 0 ≤ δ)
    (ha : ∑ k, a k ^ 2 = 1) (hb : ∑ k, b k ^ 2 = 1)
    (ha' : (∑ k, (a k - a' k) ^ 2) ≤ δ)
    (hb' : (∑ k, (b k - b' k) ^ 2) ≤ δ) :
    |(∑ k, a k * b k) - ∑ k, a' k * b' k| ≤ 2 * Real.sqrt δ + δ := by
  let e := fun k => a k - a' k
  let f := fun k => b k - b' k
  have he : Real.sqrt (∑ k, e k ^ 2) ≤ Real.sqrt δ := Real.sqrt_le_sqrt ha'
  have hf : Real.sqrt (∑ k, f k ^ 2) ≤ Real.sqrt δ := Real.sqrt_le_sqrt hb'
  have haf : |∑ k, a k * f k| ≤ Real.sqrt δ := by
    have h := abs_sum_mul_le a f
    rw [ha, Real.sqrt_one, one_mul] at h
    exact h.trans hf
  have heb : |∑ k, e k * b k| ≤ Real.sqrt δ := by
    have h := abs_sum_mul_le e b
    rw [hb, Real.sqrt_one, mul_one] at h
    exact h.trans he
  have hef : |∑ k, e k * f k| ≤ δ := by
    refine (abs_sum_mul_le e f).trans ?_
    calc
      _ ≤ Real.sqrt δ * Real.sqrt δ :=
        mul_le_mul he hf (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = δ := Real.mul_self_sqrt hδ
  have heq : (∑ k, a k * b k) - ∑ k, a' k * b' k =
      (∑ k, a k * f k) + (∑ k, e k * b k) - ∑ k, e k * f k := by
    simp only [← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    dsimp [e, f]
    ring
  rw [heq]
  have hsub := abs_sub ((∑ k, a k * f k) + ∑ k, e k * b k) (∑ k, e k * f k)
  have hadd := abs_add_le (∑ k, a k * f k) (∑ k, e k * b k)
  linarith

private theorem three_sq_le (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

private theorem critical_three_sq_le (a b c : ℝ) :
    (a + b - 2 * Real.sqrt 2 * c) ^ 2 ≤ 10 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  have h := sum_mul_sq_le_sq_mul_sq univ
    (![1, 1, -2 * Real.sqrt 2] : Fin 3 → ℝ) ![a, b, c]
  norm_num [Fin.sum_univ_succ, mul_pow, Real.sq_sqrt] at h
  nlinarith only [h]

/-- Preserving the first center keeps the star residuals stable under joint
rounding. The constants follow from the two three-term Cauchy inequalities. -/
theorem criticalStarDefect_near (x y : Fin 6 → ℝ) (h₀ : y 0 = x 0) :
    criticalStarDefect y ≤ 2 * criticalStarDefect x +
      26 * (x 1 - y 1) ^ 2 + 6 * (x 2 - y 2) ^ 2 + 6 * (x 3 - y 3) ^ 2 +
      20 * (x 4 - y 4) ^ 2 + 20 * (x 5 - y 5) ^ 2 := by
  let l := (x 1 - y 1) + (x 2 - y 2) + (x 3 - y 3)
  let r := (x 4 - y 4) + (x 5 - y 5) - 2 * Real.sqrt 2 * (x 1 - y 1)
  have hl := three_sq_le (x 1 - y 1) (x 2 - y 2) (x 3 - y 3)
  have hr := critical_three_sq_le (x 4 - y 4) (x 5 - y 5) (x 1 - y 1)
  have hleft : y 1 + y 2 + y 3 - 2 * Real.sqrt 2 * y 0 =
      (x 1 + x 2 + x 3 - 2 * Real.sqrt 2 * x 0) - l := by rw [h₀]; dsimp [l]; ring
  have hright : y 0 + y 4 + y 5 - 2 * Real.sqrt 2 * y 1 =
      (x 0 + x 4 + x 5 - 2 * Real.sqrt 2 * x 1) - r := by rw [h₀]; dsimp [r]; ring
  have hsplit (a b : ℝ) : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
    nlinarith [sq_nonneg (a + b)]
  unfold criticalStarDefect
  rw [hleft, hright]
  have h₁ := hsplit (x 1 + x 2 + x 3 - 2 * Real.sqrt 2 * x 0) l
  have h₂ := hsplit (x 0 + x 4 + x 5 - 2 * Real.sqrt 2 * x 1) r
  change l ^ 2 ≤ _ at hl
  change r ^ 2 ≤ _ at hr
  nlinarith only [hl, hr, h₁, h₂]

/-- The total star residual changes by a controlled amount when every row is
close and the first center is fixed. -/
theorem sum_criticalStarDefect_near {ι : Type*} [Fintype ι]
    (x y : Fin 6 → ι → ℝ) {δ : ℝ} (h₀ : ∀ k, y 0 k = x 0 k)
    (hnear : ∀ i, (∑ k, (x i k - y i k) ^ 2) ≤ δ) :
    (∑ k, criticalStarDefect (fun i => y i k)) ≤
      2 * (∑ k, criticalStarDefect (fun i => x i k)) + 78 * δ := by
  have h := sum_le_sum fun k (_ : k ∈ univ) =>
    criticalStarDefect_near (fun i => x i k) (fun i => y i k) (h₀ k)
  simp only [sum_add_distrib, ← mul_sum] at h
  linarith [hnear 1, hnear 2, hnear 3, hnear 4, hnear 5]

/-- Approximate ratios and approximate star saturation force the full covariance
matrix close to the symmetric model. The estimate is uniform in dimension. -/
theorem criticalStarGram_stable_approx {ι : Type*} [Fintype ι]
    (x : Fin 6 → ι → ℝ) (hx : ∀ k, 0 ≤ x 0 k)
    (hunit : ∀ i, ∑ k, x i k ^ 2 = 1) (i j : Fin 6) :
    |(∑ k, x i k * x j k) - criticalStarGram i j| ≤
      800 * (∑ k, criticalStarDefect (fun i => x i k)) +
        374700 * (∑ k, criticalStarRatioDefect (fun i => x i k)) +
        50 * Real.sqrt (12 * ∑ k, criticalStarRatioDefect (fun i => x i k)) := by
  obtain ⟨y, hy₀, hratio, hnear⟩ := exists_criticalStarRows_near x
  let δ := 12 * ∑ k, criticalStarRatioDefect (fun i => x i k)
  have hδ : 0 ≤ δ := mul_nonneg (by norm_num)
    (sum_nonneg fun k _ => criticalStarRatioDefect_nonneg _)
  have hinner (i j : Fin 6) := abs_sum_mul_sub_le_of_near (x i) (x j) (y i) (y j)
    hδ (hunit i) (hunit j) (hnear i) (hnear j)
  have hvar (i : Fin 6) : |(∑ k, y i k ^ 2) - 1| ≤ 2 * Real.sqrt δ + δ := by
    simpa only [← sq, hunit, abs_sub_comm] using hinner i i
  have hypos (k : ι) : 0 ≤ y 0 k := by rw [hy₀]; exact hx k
  have hgram := criticalStarGram_stable_of_variances y hypos hratio hvar i j
  have hstar := sum_criticalStarDefect_near x y hy₀ hnear
  have htri := abs_sub_le (∑ k, x i k * x j k) (∑ k, y i k * y j k) (criticalStarGram i j)
  dsimp [δ] at hgram
  linarith [hinner i j]

/-- The central edge and the four outer edges, with the six-row convention used
by `criticalStarGram`. -/
def criticalStarEndpoints : Fin 5 → Fin 6 × Fin 6 :=
  ![(0, 1), (0, 2), (0, 3), (1, 4), (1, 5)]

theorem criticalStarRatioDefect_eq_sum (x : Fin 6 → ℝ) :
    criticalStarRatioDefect x = ∑ e : Fin 5,
      edgeRatioError (Real.sqrt 2 / 2) (x (criticalStarEndpoints e).1)
        (x (criticalStarEndpoints e).2) := by
  simp [criticalStarRatioDefect, criticalStarEndpoints, Fin.sum_univ_succ]
  ring

/-- A covariance estimate for the actual finite distance-kernel rows. All five
adjacent correlations are assumed close to their lower bound. The remaining
error is the measured star residual, rather than an exact-ratio assumption. -/
theorem unitKernel_criticalStarGram_le {W : Type} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {D : ℕ} (hD : 2 ≤ D)
    (degree : ∀ v, H.degree v ≤ D) (v : Fin 6 → W)
    (hadj : ∀ e, H.Adj (v (criticalStarEndpoints e).1) (v (criticalStarEndpoints e).2))
    {q ε : ℝ} (hq : 1 / 2 ≤ q) (hq₁ : q ≤ 1) (hε : 0 ≤ ε) (R : ℕ)
    (htail : (D : ℝ) * ((D - 1 : ℕ) * q ^ 2) ^ R ≤ 1 / 4)
    (hcorr : ∀ e, (∑ k, unitKernel H q R (v (criticalStarEndpoints e).1) k *
        unitKernel H q R (v (criticalStarEndpoints e).2) k) ≤
      2 * q / (1 + q ^ 2) + ε) (i j : Fin 6) :
    let η := 5 * (96 * ε + 32 * D * ((D - 1 : ℕ) * q ^ 2) ^ R +
      4 * (Real.sqrt 2 / 2 - q) ^ 2)
    |(∑ k, unitKernel H q R (v i) k * unitKernel H q R (v j) k) - criticalStarGram i j| ≤
      800 * (∑ k, criticalStarDefect (fun i => unitKernel H q R (v i) k)) +
        374700 * η + 50 * Real.sqrt (12 * η) := by
  let x := fun i k => unitKernel H q R (v i) k
  let B := 96 * ε + 32 * D * ((D - 1 : ℕ) * q ^ 2) ^ R + 4 * (Real.sqrt 2 / 2 - q) ^ 2
  have hratio : (∑ k, criticalStarRatioDefect (fun i => x i k)) ≤ 5 * B := by
    simp_rw [criticalStarRatioDefect_eq_sum]
    rw [sum_comm]
    calc
      _ ≤ ∑ _e : Fin 5, B := by
        apply sum_le_sum
        intro e _
        exact sum_unitKernel_criticalRatioError_le H hD degree hq hq₁ hε R
          (hadj e) htail (hcorr e)
      _ = 5 * B := by simp
  have hx : ∀ k, 0 ≤ x 0 k := fun k => unitKernel_nonneg H (by linarith) R (v 0) k
  have h := criticalStarGram_stable_approx x hx (fun i => sum_unitKernel_sq H q R (v i)) i j
  have hsqrt := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 12))
  change |(∑ k, x i k * x j k) - criticalStarGram i j| ≤
    800 * (∑ k, criticalStarDefect (fun i => x i k)) + 374700 * (5 * B) +
      50 * Real.sqrt (12 * (5 * B))
  linarith

/-- The two centers in the six-row convention. -/
def criticalStarCenter : Fin 2 → Fin 6 := ![0, 1]

/-- The three neighbors of each center, with the shared edge represented at both ends. -/
def criticalStarNeighbors : Fin 2 → Fin 3 → Fin 6 := ![![1, 2, 3], ![0, 4, 5]]

/-- A covariance estimate controlled by the two edge-star gaps. Correlation upper bounds
and vertex-star residual bounds now follow from those gaps instead of being separate
hypotheses. The Gaussian probability and global layout estimates are still separate. -/
theorem unitKernel_criticalStarGram_le_of_gaps {W : Type} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj] {D : ℕ} (hD : 2 ≤ D)
    (degree : ∀ v, H.degree v ≤ D) (v : Fin 6 → W)
    (hadj : ∀ e, H.Adj (v (criticalStarEndpoints e).1) (v (criticalStarEndpoints e).2))
    {q κ g : ℝ} (hq : 1 / 2 ≤ q) (hq₁ : q ≤ 1) (hg : 0 ≤ g)
    (hκ : 1 / 2 ≤ κ) (hκ₁ : κ ≤ 1) (hbase : 2 * κ ^ 2 - 1 ≤ 2 * q / (1 + q ^ 2))
    (R : ℕ) (htail : (D : ℝ) * ((D - 1 : ℕ) * q ^ 2) ^ R ≤ 1 / 4)
    (hpos : ∀ b j, 0 < pairNormSq H q R
      (v (criticalStarNeighbors b j)) (v (criticalStarCenter b)))
    (hinner : ∀ b j, κ ≤ ∑ k,
      edgeVector H q R s(v (criticalStarNeighbors b j), v (criticalStarCenter b)) k *
        unitKernel H q R (v (criticalStarCenter b)) k)
    (hgap : ∀ b, starGap κ (fun j => edgeVector H q R
      s(v (criticalStarNeighbors b j), v (criticalStarCenter b))) ≤ g) (i j : Fin 6) :
    let η := 5 * (128 * g + 32 * D * ((D - 1 : ℕ) * q ^ 2) ^ R +
      4 * (Real.sqrt 2 / 2 - q) ^ 2)
    |(∑ k, unitKernel H q R (v i) k * unitKernel H q R (v j) k) - criticalStarGram i j| ≤
      800 * (64 * g + 4 * (3 * (2 * κ ^ 2 - 1) - 2 * Real.sqrt 2) ^ 2) +
        374700 * η + 50 * Real.sqrt (12 * η) := by
  have hc (b : Fin 2) (l : Fin 3) :
      (∑ k, unitKernel H q R (v (criticalStarNeighbors b l)) k *
        unitKernel H q R (v (criticalStarCenter b)) k) ≤ 2 * q / (1 + q ^ 2) + 4 / 3 * g := by
    have h := unitKernel_correlation_le_starGap H (v (criticalStarCenter b))
      (fun l => v (criticalStarNeighbors b l)) (hpos b) hκ hκ₁ (hinner b) l
    linarith [hgap b]
  have hcorr (e : Fin 5) :
      (∑ k, unitKernel H q R (v (criticalStarEndpoints e).1) k *
        unitKernel H q R (v (criticalStarEndpoints e).2) k) ≤
          2 * q / (1 + q ^ 2) + 4 / 3 * g := by
    fin_cases e
    · simpa [criticalStarEndpoints, criticalStarNeighbors, criticalStarCenter, mul_comm]
        using hc 0 0
    · simpa [criticalStarEndpoints, criticalStarNeighbors, criticalStarCenter, mul_comm]
        using hc 0 1
    · simpa [criticalStarEndpoints, criticalStarNeighbors, criticalStarCenter, mul_comm]
        using hc 0 2
    · simpa [criticalStarEndpoints, criticalStarNeighbors, criticalStarCenter, mul_comm]
        using hc 1 1
    · simpa [criticalStarEndpoints, criticalStarNeighbors, criticalStarCenter, mul_comm]
        using hc 1 2
  have hr (b : Fin 2) :
      (∑ k, ((∑ l, unitKernel H q R (v (criticalStarNeighbors b l)) k) -
        2 * Real.sqrt 2 * unitKernel H q R (v (criticalStarCenter b)) k) ^ 2) ≤
          32 * g + 2 * (3 * (2 * κ ^ 2 - 1) - 2 * Real.sqrt 2) ^ 2 := by
    have h := unitKernel_critical_star_residual_le H (v (criticalStarCenter b))
      (fun l => v (criticalStarNeighbors b l)) (hpos b) hκ hκ₁ (hinner b)
    linarith [hgap b]
  have hE : (∑ k, criticalStarDefect (fun l => unitKernel H q R (v l) k)) ≤
      64 * g + 4 * (3 * (2 * κ ^ 2 - 1) - 2 * Real.sqrt 2) ^ 2 := by
    have h₀ := hr 0
    have h₁ := hr 1
    simp [criticalStarNeighbors, criticalStarCenter, Fin.sum_univ_succ, ← add_assoc] at h₀ h₁
    simp only [criticalStarDefect, sum_add_distrib]
    linarith
  have h := unitKernel_criticalStarGram_le H hD degree v hadj hq hq₁
    (show 0 ≤ 4 / 3 * g by positivity) R htail hcorr i j
  dsimp only at h ⊢
  have he : 96 * (4 / 3 * g) = 128 * g := by ring
  rw [he] at h
  linarith

end Frontier.Gaussian
