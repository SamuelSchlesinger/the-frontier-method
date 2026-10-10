/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.GaussianStability
public import Frontier.Layouts.GaussianQuantitative
public import Frontier.Layouts.KernelCovariance

/-!
# Robust pair costs for finite kernel rows

The six-vertex covariance certificate controls the four normalized outer edge
scores. Normalization is continuous at the critical covariance, where all four
denominators are strictly positive. The robust Gaussian pair estimate therefore
applies to finite kernels with sufficiently small covariance errors.
-/

@[expose] public section

namespace Frontier.Gaussian

open MeasureTheory Set

private def outerCenter : Fin 4 → Fin 6 := ![0, 0, 1, 1]
private def outerNeighbor : Fin 4 → Fin 6 := ![2, 3, 4, 5]

private noncomputable def outerPortCovariance (A : Fin 6 → Fin 6 → ℝ)
    (i j : Fin 4) : ℝ :=
  (A (outerCenter i) (outerCenter j) + A (outerCenter i) (outerNeighbor j) +
    A (outerNeighbor i) (outerCenter j) + A (outerNeighbor i) (outerNeighbor j)) /
      (Real.sqrt (2 + 2 * A (outerCenter i) (outerNeighbor i)) *
        Real.sqrt (2 + 2 * A (outerCenter j) (outerNeighbor j)))

private theorem critical_outer_norm (i : Fin 4) :
    2 + 2 * criticalStarGram (outerCenter i) (outerNeighbor i) =
      2 + 4 * Real.sqrt 2 / 3 := by
  fin_cases i <;> norm_num [outerCenter, outerNeighbor, criticalStarGram] <;> ring

private theorem outerPortCovariance_critical (i j : Fin 4) (hij : i < j) :
    outerPortCovariance criticalStarGram i j =
      if (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3) then (1 + 2 * Real.sqrt 2) / 4
        else (2 + Real.sqrt 2) / 4 := by
  have hden : 0 < 2 + 4 * Real.sqrt 2 / 3 := by positivity
  simp only [outerPortCovariance, critical_outer_norm, ← sq, Real.sq_sqrt hden.le]
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals
    norm_num [outerCenter, outerNeighbor, criticalStarGram]
    field_simp
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

private theorem sqrt_error_le {a b δ : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : |a - b| ≤ 2 * δ) : |Real.sqrt a - Real.sqrt b| ≤ δ := by
  have hsa : 1 ≤ Real.sqrt a := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa)
  have hsb : 1 ≤ Real.sqrt b := (Real.le_sqrt (by norm_num) (by linarith)).mpr (by simpa)
  have he : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
    nlinarith [Real.sq_sqrt (by linarith : 0 ≤ a), Real.sq_sqrt (by linarith : 0 ≤ b)]
  have habs : |Real.sqrt a - Real.sqrt b| * (Real.sqrt a + Real.sqrt b) = |a - b| := by
    rw [← abs_of_nonneg (show 0 ≤ Real.sqrt a + Real.sqrt b by positivity), ← abs_mul, he]
  nlinarith [mul_nonneg (abs_nonneg (Real.sqrt a - Real.sqrt b))
    (show 0 ≤ Real.sqrt a + Real.sqrt b - 2 by linarith)]

private theorem ratio_error_le {N D N₀ D₀ δ : ℝ} (hδ : 0 ≤ δ)
    (hD : 1 ≤ D) (hD₀ : 1 ≤ D₀) (hN₀ : |N₀| ≤ 4)
    (hN : |N - N₀| ≤ 4 * δ) (hden : |D - D₀| ≤ 6 * δ) :
    |N / D - N₀ / D₀| ≤ 28 * δ := by
  have hDp : 0 < D := by linarith
  have hD₀p : 0 < D₀ := by linarith
  have he : N / D - N₀ / D₀ = ((N - N₀) * D₀ + N₀ * (D₀ - D)) / (D * D₀) := by
    field_simp
    ring
  rw [he, abs_div, abs_of_pos (mul_pos hDp hD₀p), div_le_iff₀ (mul_pos hDp hD₀p)]
  calc
    _ ≤ |N - N₀| * D₀ + |N₀| * |D₀ - D| := by
      simpa only [abs_mul, abs_of_pos hD₀p] using abs_add_le ((N - N₀) * D₀) (N₀ * (D₀ - D))
    _ ≤ 4 * δ * D₀ + 4 * (6 * δ) := by
      gcongr
      simpa only [abs_sub_comm] using hden
    _ ≤ 28 * δ * D₀ := by nlinarith
    _ ≤ (28 * δ * D₀) * D := le_mul_of_one_le_right (by positivity) hD
    _ = _ := by ring

/-- Normalizing the four edge ports amplifies an entrywise covariance error
of at most `δ ≤ 1/4` by at most a factor of 28. -/
private theorem outerPortCovariance_error {δ : ℝ} (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 4)
    (A : Fin 6 → Fin 6 → ℝ) (hA : ∀ i j, |A i j - criticalStarGram i j| ≤ δ) :
    (∀ i, 0 < 2 + 2 * A (outerCenter i) (outerNeighbor i)) ∧
      ∀ i j, |outerPortCovariance A i j - outerPortCovariance criticalStarGram i j| ≤ 28 * δ := by
  let D (i : Fin 4) := 2 + 2 * A (outerCenter i) (outerNeighbor i)
  let d := 2 + 4 * Real.sqrt 2 / 3
  have hslo : 1 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hshi : Real.sqrt 2 ≤ 3 / 2 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  have hd : 3 ≤ d ∧ d ≤ 4 := by dsimp [d]; constructor <;> linarith
  have hdiff (i) : |D i - d| ≤ 2 * δ := by
    have he := critical_outer_norm i
    have h := abs_le.mp (hA (outerCenter i) (outerNeighbor i))
    dsimp [D, d]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hD (i) : 1 ≤ D i ∧ D i ≤ 9 := by
    have h := abs_le.mp (hdiff i)
    constructor <;> linarith
  have hroot (i) : 1 ≤ Real.sqrt (D i) ∧ Real.sqrt (D i) ≤ 3 :=
    ⟨(Real.le_sqrt (by norm_num) (by linarith [(hD i).1])).mpr (by simpa using (hD i).1),
      (Real.sqrt_le_left (by norm_num)).mpr (by norm_num; exact (hD i).2)⟩
  have hroot₀ : 1 ≤ Real.sqrt d ∧ Real.sqrt d ≤ 3 :=
    ⟨(Real.le_sqrt (by norm_num) (by linarith)).mpr (by linarith),
      (Real.sqrt_le_left (by norm_num)).mpr (by linarith)⟩
  have hnear (i) := sqrt_error_le (hD i).1 (show 1 ≤ d by linarith) (hdiff i)
  have hbase (i j : Fin 6) : |criticalStarGram i j| ≤ 1 := by
    fin_cases i <;> fin_cases j <;> norm_num [criticalStarGram]
    all_goals rw [abs_le]; constructor <;> linarith [Real.sqrt_nonneg 2]
  refine ⟨fun i => by change 0 < D i; linarith [(hD i).1], fun i j => ?_⟩
  let num (A : Fin 6 → Fin 6 → ℝ) :=
    A (outerCenter i) (outerCenter j) + A (outerCenter i) (outerNeighbor j) +
      A (outerNeighbor i) (outerCenter j) + A (outerNeighbor i) (outerNeighbor j)
  have hnum : |num A - num criticalStarGram| ≤ 4 * δ := by
    have h₁ := abs_le.mp (hA (outerCenter i) (outerCenter j))
    have h₂ := abs_le.mp (hA (outerCenter i) (outerNeighbor j))
    have h₃ := abs_le.mp (hA (outerNeighbor i) (outerCenter j))
    have h₄ := abs_le.mp (hA (outerNeighbor i) (outerNeighbor j))
    dsimp [num]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hnum₀ : |num criticalStarGram| ≤ 4 := by
    have h₁ := abs_le.mp (hbase (outerCenter i) (outerCenter j))
    have h₂ := abs_le.mp (hbase (outerCenter i) (outerNeighbor j))
    have h₃ := abs_le.mp (hbase (outerNeighbor i) (outerCenter j))
    have h₄ := abs_le.mp (hbase (outerNeighbor i) (outerNeighbor j))
    dsimp [num]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hden : |Real.sqrt (D i) * Real.sqrt (D j) - Real.sqrt d * Real.sqrt d| ≤ 6 * δ := by
    have he : Real.sqrt (D i) * Real.sqrt (D j) - Real.sqrt d * Real.sqrt d =
        Real.sqrt (D i) * (Real.sqrt (D j) - Real.sqrt d) +
          (Real.sqrt (D i) - Real.sqrt d) * Real.sqrt d := by ring
    rw [he]
    calc
      _ ≤ Real.sqrt (D i) * |Real.sqrt (D j) - Real.sqrt d| +
          |Real.sqrt (D i) - Real.sqrt d| * Real.sqrt d := by
        simpa only [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] using
          abs_add_le (Real.sqrt (D i) * (Real.sqrt (D j) - Real.sqrt d))
            ((Real.sqrt (D i) - Real.sqrt d) * Real.sqrt d)
      _ ≤ 3 * δ + δ * 3 := add_le_add
        (mul_le_mul (hroot i).2 (hnear j) (abs_nonneg _) (by norm_num))
        (mul_le_mul (hnear i) hroot₀.2 (Real.sqrt_nonneg _) hδ)
      _ = _ := by ring
  have h := ratio_error_le hδ
    (show 1 ≤ Real.sqrt (D i) * Real.sqrt (D j) by nlinarith [(hroot i).1, (hroot j).1])
    (show 1 ≤ Real.sqrt d * Real.sqrt d by nlinarith [hroot₀.1]) hnum₀ hnum hden
  simpa only [outerPortCovariance, critical_outer_norm, num, D, d] using h

private theorem exists_outerPortCovariance_tolerance {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ A : Fin 6 → Fin 6 → ℝ,
      (∀ i j, |A i j - criticalStarGram i j| < δ) →
      (∀ i, 0 < 2 + 2 * A (outerCenter i) (outerNeighbor i)) ∧
      ∀ i j, i < j → |outerPortCovariance A i j -
        outerPortCovariance criticalStarGram i j| < ε := by
  have hd (i : Fin 4) : 0 < 2 + 2 * criticalStarGram (outerCenter i) (outerNeighbor i) := by
    rw [critical_outer_norm]
    positivity
  have hc (i j : Fin 4) : ContinuousAt (fun A => outerPortCovariance A i j) criticalStarGram := by
    unfold outerPortCovariance
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact mul_ne_zero (Real.sqrt_pos.mpr (hd i)).ne' (Real.sqrt_pos.mpr (hd j)).ne'
  have hpos : ∀ᶠ A in nhds criticalStarGram,
      ∀ i, 0 < 2 + 2 * A (outerCenter i) (outerNeighbor i) := by
    refine Filter.eventually_all.mpr fun i => ?_
    have hc : Continuous (fun A : Fin 6 → Fin 6 → ℝ =>
        2 + 2 * A (outerCenter i) (outerNeighbor i)) := by fun_prop
    exact hc.continuousAt.eventually (Ioi_mem_nhds (hd i))
  have hnear : ∀ᶠ A in nhds criticalStarGram,
      ∀ i j, |outerPortCovariance A i j - outerPortCovariance criticalStarGram i j| < ε := by
    refine Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ?_
    have h := ((hc i j).sub_const (outerPortCovariance criticalStarGram i j)).abs
    exact h.eventually (Iio_mem_nhds (by simpa using hε))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hpos.and hnear)
  refine ⟨δ, hδ, fun A hA => ?_⟩
  have ha : A ∈ Metric.ball criticalStarGram δ :=
    (dist_pi_lt_iff hδ).mpr fun i => (dist_pi_lt_iff hδ).mpr fun j => by
      simpa only [Real.dist_eq] using hA i j
  exact ⟨(hball ha).1, fun i j _ => (hball ha).2 i j⟩

/-- Small errors in the six vertex covariances suffice for the local pair
estimate on the actual normalized edge vectors. No exact critical ratios or
limiting Gaussian realization are assumed. -/
theorem exists_unitKernel_pair_tolerance {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ {W : Type} [Fintype W] (H : SimpleGraph W)
      (q : ℝ) (R : ℕ) (v : Fin 6 → W),
      (∀ i j, |(∑ k, unitKernel H q R (v i) k * unitKernel H q R (v j) k) -
        criticalStarGram i j| < δ) →
      ∀ t, (∫ ω, twoVertexThresholdCost t (fun i => form
        (edgeVector H q R s(v (![0, 0, 1, 1] i), v (![2, 3, 4, 5] i))) ω)
          ∂gaussPi W) ≤ twoVertexTreeBound + ε := by
  obtain ⟨ε', hε', htree⟩ := exists_twoVertexTree_tolerance hε
  obtain ⟨δ, hδ, hports⟩ := exists_outerPortCovariance_tolerance hε'
  refine ⟨δ, hδ, fun {W} _ H q R v hgram t => ?_⟩
  let A := fun i j => ∑ k, unitKernel H q R (v i) k * unitKernel H q R (v j) k
  obtain ⟨hpos, hcov⟩ := hports A hgram
  let a := fun i => edgeVector H q R s(v (outerCenter i), v (outerNeighbor i))
  have hn (i) : pairNormSq H q R (v (outerCenter i)) (v (outerNeighbor i)) =
      2 + 2 * A (outerCenter i) (outerNeighbor i) := pairNormSq_eq H q R _ _
  have hu (i) : ∑ k, a i k ^ 2 = 1 := sum_edgeVector_sq (by rw [hn]; exact hpos i)
  have he (i j) : ∑ k, a i k * a j k = outerPortCovariance A i j := by
    simp only [a, edgeVector_mk, hn, div_mul_div_comm, ← Finset.sum_div,
      add_mul, mul_add, Finset.sum_add_distrib, outerPortCovariance, A]
    congr 1
    ring
  apply htree a hu
  intro i j hij
  rw [he, ← outerPortCovariance_critical i j hij]
  exact hcov i j hij

/-- A six-vertex covariance error of `10⁻¹⁶` preserves the explicit pair estimate. -/
theorem unitKernel_pair_explicit {W : Type} [Fintype W] (H : SimpleGraph W)
    (q : ℝ) (R : ℕ) (v : Fin 6 → W)
    (hgram : ∀ i j, |(∑ k, unitKernel H q R (v i) k * unitKernel H q R (v j) k) -
      criticalStarGram i j| ≤ 1 / 10 ^ 16) (t : ℝ) :
    (∫ ω, twoVertexThresholdCost t (fun i => form
      (edgeVector H q R s(v (![0, 0, 1, 1] i), v (![2, 3, 4, 5] i))) ω)
        ∂gaussPi W) ≤ twoVertexTreeBound + 1 / 5000 := by
  let A := fun i j => ∑ k, unitKernel H q R (v i) k * unitKernel H q R (v j) k
  obtain ⟨hpos, hcov⟩ := outerPortCovariance_error
    (by norm_num : (0 : ℝ) ≤ 1 / 10 ^ 16) (by norm_num) A hgram
  let a := fun i => edgeVector H q R s(v (outerCenter i), v (outerNeighbor i))
  have hn (i) : pairNormSq H q R (v (outerCenter i)) (v (outerNeighbor i)) =
      2 + 2 * A (outerCenter i) (outerNeighbor i) := pairNormSq_eq H q R _ _
  have hu (i) : ∑ k, a i k ^ 2 = 1 := sum_edgeVector_sq (by rw [hn]; exact hpos i)
  have he (i j) : ∑ k, a i k * a j k = outerPortCovariance A i j := by
    simp only [a, edgeVector_mk, hn, div_mul_div_comm, ← Finset.sum_div,
      add_mul, mul_add, Finset.sum_add_distrib, outerPortCovariance, A]
    congr 1
    ring
  apply integral_twoVertexThresholdCost_le_tree_explicit a hu
  have hupper (i j : Fin 4) (hij : i ≤ j) :
      |(∑ k, a i k * a j k) - treePortGram i j| ≤ 1 / 10 ^ 14 := by
    rcases hij.eq_or_lt with rfl | hij
    · simp only [← sq, hu, treePortGram_diag, sub_self, abs_zero]
      positivity
    · rw [he, treePortGram_of_lt i j hij, ← outerPortCovariance_critical i j hij]
      exact (hcov i j).trans (by norm_num)
  intro i j
  rcases le_total i j with h | h
  · exact hupper i j h
  · simpa only [mul_comm, treePortGram_symm j i] using hupper j i h

/-- The explicit common tolerance for star gaps and finite-kernel errors. -/
noncomputable def pairGapTolerance : ℝ := 1 / 10 ^ 44

theorem pairGapTolerance_pos : 0 < pairGapTolerance := by norm_num [pairGapTolerance]

/-- The quantitative covariance estimate closes at the explicit tolerance `10⁻⁴⁴`. -/
theorem unitKernel_pair_gap_explicit {W : Type} [Fintype W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (degree : ∀ v, H.degree v ≤ 3) (v : Fin 6 → W)
    (hadj : ∀ e, H.Adj (v (criticalStarEndpoints e).1) (v (criticalStarEndpoints e).2))
    (q κ : ℝ) (hq : 1 / 2 ≤ q) (hq₁ : q ≤ 1) (hκ : 1 / 2 ≤ κ) (hκ₁ : κ ≤ 1)
    (hbase : 2 * κ ^ 2 - 1 ≤ 2 * q / (1 + q ^ 2))
    (R : ℕ) (htail : 3 * (2 * q ^ 2) ^ R ≤ 1 / 4)
    (htail' : 3 * (2 * q ^ 2) ^ R ≤ pairGapTolerance)
    (hqnear : |Real.sqrt 2 / 2 - q| ≤ pairGapTolerance)
    (hκnear : |3 * (2 * κ ^ 2 - 1) - 2 * Real.sqrt 2| ≤ pairGapTolerance)
    (hpos : ∀ b j, 0 < pairNormSq H q R
      (v (criticalStarNeighbors b j)) (v (criticalStarCenter b)))
    (hinner : ∀ b j, κ ≤ ∑ k,
      edgeVector H q R s(v (criticalStarNeighbors b j), v (criticalStarCenter b)) k *
        unitKernel H q R (v (criticalStarCenter b)) k)
    (hgap : ∀ b, starGap κ (fun j => edgeVector H q R
      s(v (criticalStarNeighbors b j), v (criticalStarCenter b))) ≤ pairGapTolerance)
    (t : ℝ) :
    (∫ ω, twoVertexThresholdCost t (fun i => form
      (edgeVector H q R s(v (![0, 0, 1, 1] i), v (![2, 3, 4, 5] i))) ω)
        ∂gaussPi W) ≤ twoVertexTreeBound + 1 / 5000 := by
  apply unitKernel_pair_explicit H q R v
  intro i j
  have hτ := pairGapTolerance_pos.le
  have hc := unitKernel_criticalStarGram_le_of_gaps H (by norm_num : 2 ≤ 3)
    degree v hadj hq hq₁ hτ hκ hκ₁ hbase R (by simpa using htail) hpos hinner hgap i j
  norm_num only [Nat.cast_ofNat, Nat.reduceSub] at hc
  have hqsq : (Real.sqrt 2 / 2 - q) ^ 2 ≤ pairGapTolerance ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hτ).mpr hqnear
  have hκsq : (3 * (2 * κ ^ 2 - 1) - 2 * Real.sqrt 2) ^ 2 ≤ pairGapTolerance ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hτ).mpr hκnear
  have hη : 5 * (128 * pairGapTolerance + 32 * 3 * (2 * q ^ 2) ^ R +
      4 * (Real.sqrt 2 / 2 - q) ^ 2) ≤
        5 * (128 * pairGapTolerance + 32 * pairGapTolerance + 4 * pairGapTolerance ^ 2) := by
    nlinarith only [htail', hqsq]
  have hsqrt := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hη (by norm_num : (0 : ℝ) ≤ 12))
  have hsmall : Real.sqrt (12 * (5 * (128 * pairGapTolerance + 32 * pairGapTolerance +
      4 * pairGapTolerance ^ 2))) ≤ 1 / 10 ^ 20 := by
    apply (Real.sqrt_le_left (by norm_num)).mpr
    norm_num [pairGapTolerance]
  have hfinal : 800 * (64 * pairGapTolerance + 4 * pairGapTolerance ^ 2) +
      374700 * (5 * (128 * pairGapTolerance + 32 * pairGapTolerance +
        4 * pairGapTolerance ^ 2)) + 50 * (1 / 10 ^ 20) ≤ (1 : ℝ) / 10 ^ 16 := by
    norm_num [pairGapTolerance]
  nlinarith only [hc, hκsq, hη, hsqrt, hsmall, hfinal]

open scoped Topology in
/-- Small star gaps and small kernel-approximation errors suffice uniformly for
the pair estimate on finite subcubic graphs. The single tolerance can be chosen
before the graph, the radius, the six vertices, and the threshold. -/
theorem exists_unitKernel_pair_gap_tolerance {ε : ℝ} (hε : 0 < ε) :
    ∃ τ > 0, ∀ {W : Type} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj]
      (_degree : ∀ v, H.degree v ≤ 3) (v : Fin 6 → W)
      (_hadj : ∀ e, H.Adj (v (criticalStarEndpoints e).1) (v (criticalStarEndpoints e).2))
      (q κ : ℝ), 1 / 2 ≤ q → q ≤ 1 → 1 / 2 ≤ κ → κ ≤ 1 →
      2 * κ ^ 2 - 1 ≤ 2 * q / (1 + q ^ 2) →
      ∀ R : ℕ, 3 * (2 * q ^ 2) ^ R ≤ 1 / 4 → 3 * (2 * q ^ 2) ^ R ≤ τ →
      |Real.sqrt 2 / 2 - q| ≤ τ → |3 * (2 * κ ^ 2 - 1) - 2 * Real.sqrt 2| ≤ τ →
      (∀ b j, 0 < pairNormSq H q R
        (v (criticalStarNeighbors b j)) (v (criticalStarCenter b))) →
      (∀ b j, κ ≤ ∑ k,
        edgeVector H q R s(v (criticalStarNeighbors b j), v (criticalStarCenter b)) k *
          unitKernel H q R (v (criticalStarCenter b)) k) →
      (∀ b, starGap κ (fun j => edgeVector H q R
        s(v (criticalStarNeighbors b j), v (criticalStarCenter b))) ≤ τ) →
      ∀ t, (∫ ω, twoVertexThresholdCost t (fun i => form
        (edgeVector H q R s(v (![0, 0, 1, 1] i), v (![2, 3, 4, 5] i))) ω)
          ∂gaussPi W) ≤ twoVertexTreeBound + ε := by
  obtain ⟨δ, hδ, hnear⟩ := exists_unitKernel_pair_tolerance hε
  let F := fun τ : ℝ =>
    800 * (64 * τ + 4 * τ ^ 2) + 374700 * (5 * (128 * τ + 32 * τ + 4 * τ ^ 2)) +
      50 * Real.sqrt (12 * (5 * (128 * τ + 32 * τ + 4 * τ ^ 2)))
  have hF : Continuous F := by dsimp [F]; fun_prop
  have hsmall : ∀ᶠ τ in 𝓝 (0 : ℝ), F τ < δ :=
    hF.continuousAt.eventually (Iio_mem_nhds (by simpa [F] using hδ))
  obtain ⟨τ, hτF, hτ⟩ := ((hsmall.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : ∀ᶠ τ in 𝓝[>] (0 : ℝ), 0 < τ)).exists
  refine ⟨τ, hτ, fun {W} _ H _ degree v hadj q κ hq hq₁ hκ hκ₁ hbase
    R htail htail' hqnear hκnear hpos hinner hgap t => ?_⟩
  apply hnear H q R v
  intro i j
  have hc := unitKernel_criticalStarGram_le_of_gaps H (by norm_num : 2 ≤ 3)
    degree v hadj hq hq₁ hτ.le hκ hκ₁ hbase R (by simpa using htail)
    hpos hinner hgap i j
  norm_num only [Nat.cast_ofNat, Nat.reduceSub] at hc
  have hqsq : (Real.sqrt 2 / 2 - q) ^ 2 ≤ τ ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hτ.le).mpr hqnear
  have hκsq : (3 * (2 * κ ^ 2 - 1) - 2 * Real.sqrt 2) ^ 2 ≤ τ ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hτ.le).mpr hκnear
  have hη : 5 * (128 * τ + 32 * 3 * (2 * q ^ 2) ^ R +
      4 * (Real.sqrt 2 / 2 - q) ^ 2) ≤ 5 * (128 * τ + 32 * τ + 4 * τ ^ 2) := by
    nlinarith only [htail', hqsq]
  refine hc.trans_lt (lt_of_le_of_lt ?_ hτF)
  have hsqrt := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hη (by norm_num : (0 : ℝ) ≤ 12))
  dsimp [F]
  nlinarith only [hκsq, hη, hsqrt]

open scoped Topology in
/-- One finite kernel can meet the original straddle estimate and arbitrarily
small pair-approximation tolerances simultaneously. The parameters are chosen
before the graph. -/
theorem exists_pair_kernel_parameters {τ ξ : ℝ} (hτ : 0 < τ) (hξ : 0 < ξ) :
    ∃ (q : ℝ) (R : ℕ) (ρ : ℝ),
      1 / 2 ≤ q ∧ q ≤ 1 ∧ 17 / 32 ≤ ρ ∧ ρ < 2 * Real.sqrt 2 / 3 ∧
      ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ∧
      3 * (2 * q ^ 2) ^ R ≤ 1 / 4 ∧ 3 * (2 * q ^ 2) ^ R ≤ τ ∧
      |Real.sqrt 2 / 2 - q| ≤ τ ∧ |3 * ρ - 2 * Real.sqrt 2| ≤ τ ∧
      straddleBound ρ ≤ gaussianCoefficient + ξ := by
  let g := 2 * Real.sqrt 2 / 3
  let q₀ := Real.sqrt 2 / 2
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hslo : 1 < Real.sqrt 2 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hshi : Real.sqrt 2 < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hglo : 17 / 32 < g := by dsimp [g]; linarith only [hslo]
  have hqlo : 1 / 2 < q₀ := by dsimp [q₀]; linarith only [hslo]
  have hqhi : q₀ < 1 := by dsimp [q₀]; linarith only [hshi]
  have hstraddle : Continuous straddleBound := by unfold straddleBound; fun_prop
  have hcorr : Continuous (fun q : ℝ => 2 * q / (1 + q ^ 2)) := by
    apply Continuous.div <;> first | fun_prop | exact fun q => by positivity
  have hlim : 2 * q₀ / (1 + q₀ ^ 2) = g := by
    dsimp [q₀, g]
    field_simp
    nlinarith only [hs]
  have hnear : ∀ᶠ ρ in 𝓝 g,
      17 / 32 < ρ ∧ |3 * ρ - 2 * Real.sqrt 2| < τ ∧
      straddleBound ρ < gaussianCoefficient + ξ := by
    have hlo : ∀ᶠ ρ in 𝓝 g, 17 / 32 < ρ := Ioi_mem_nhds hglo
    have hd : Continuous (fun ρ : ℝ => |3 * ρ - 2 * Real.sqrt 2|) := by fun_prop
    have hd0 : |3 * g - 2 * Real.sqrt 2| = 0 := by dsimp [g]; ring_nf; norm_num
    have he : ∀ᶠ ρ in 𝓝 g, |3 * ρ - 2 * Real.sqrt 2| < τ :=
      hd.continuousAt.eventually (Iio_mem_nhds (by simpa only [hd0] using hτ))
    have hc : ∀ᶠ ρ in 𝓝 g, straddleBound ρ < gaussianCoefficient + ξ :=
      hstraddle.continuousAt.eventually
      (Iio_mem_nhds (by rw [← gaussianCoefficient_eq]; linarith only [hξ]))
    exact hlo.and (he.and hc)
  obtain ⟨ρ, ⟨hρlo, hρnear, hρcost⟩, hρhi⟩ := ((hnear.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : ∀ᶠ ρ in 𝓝[<] g, ρ < g)).exists
  have hqnear : ∀ᶠ q in 𝓝 q₀,
      1 / 2 < q ∧ |q₀ - q| < τ ∧ ρ < 2 * q / (1 + q ^ 2) := by
    have hlo : ∀ᶠ q in 𝓝 q₀, 1 / 2 < q := Ioi_mem_nhds hqlo
    have hd : Continuous (fun q : ℝ => |q₀ - q|) := by fun_prop
    have he : ∀ᶠ q in 𝓝 q₀, |q₀ - q| < τ :=
      hd.continuousAt.eventually (Iio_mem_nhds (by simpa using hτ))
    have hc : ∀ᶠ q in 𝓝 q₀, ρ < 2 * q / (1 + q ^ 2) :=
      hcorr.continuousAt.eventually (Ioi_mem_nhds (by simpa only [hlim] using hρhi))
    exact hlo.and (he.and hc)
  obtain ⟨q, ⟨hq, hqnear, hqρ⟩, hq₀⟩ := ((hqnear.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : ∀ᶠ q in 𝓝[<] q₀, q < q₀)).exists
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hdecay : 2 * q ^ 2 < 1 := by
    have hsq := (sq_lt_sq₀ hq0 (hq0.trans hq₀.le)).mpr hq₀
    dsimp [q₀] at hsq
    nlinarith only [hsq, hs]
  let η := min (min τ (1 / 4)) (2 * q / (1 + q ^ 2) - ρ)
  have hη : 0 < η := lt_min (lt_min hτ (by norm_num)) (sub_pos.mpr hqρ)
  obtain ⟨R, hR⟩ := exists_pow_lt_of_lt_one (show 0 < η / 3 by positivity) hdecay
  have htail : 3 * (2 * q ^ 2) ^ R < η := by linarith only [hR]
  have hητ : η ≤ τ := (min_le_left _ _).trans (min_le_left _ _)
  have hη₁ : η ≤ 1 / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hηρ : η ≤ 2 * q / (1 + q ^ 2) - ρ := min_le_right _ _
  exact ⟨q, R, ρ, hq.le, (hq₀.trans hqhi).le, hρlo.le, hρhi,
    by linarith only [htail, hηρ], (htail.trans_le hη₁).le, (htail.trans_le hητ).le,
    hqnear.le, hρnear.le, hρcost.le⟩

end Frontier.Gaussian
