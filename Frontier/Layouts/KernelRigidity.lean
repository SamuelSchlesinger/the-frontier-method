/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.GaussianPatch
public import Frontier.Layouts.KernelStability

/-!
# Rigidity of two saturated distance-kernel stars

At the critical ratio, an edge of a distance kernel changes a nonzero coordinate
by `√2` or its reciprocal. If each of two adjacent cubic stars has exactly the
limiting eigenvector sum, their six coordinate values have only four possible
shapes, one for each outer branch. Unit row variances then fix the weights of
these shapes. This supplies covariance information that star correlations alone
do not contain.

The quantitative version bounds every covariance error by the squared star
residuals and variance errors, independently of the number of coordinates.
`exists_criticalStarRows_near` rounds approximate ratios jointly along the two
stars. `KernelStability` controls the ratio error of finite kernels, and
`KernelCovariance` combines these results into a covariance estimate.
-/

@[expose] public section

namespace Frontier.Gaussian

open Finset MeasureTheory

/-- The two possible ratios on an edge when the distances differ by one. -/
noncomputable def criticalRatio (high : Bool) : ℝ :=
  if high then Real.sqrt 2 else Real.sqrt 2 / 2

theorem criticalRatio_pos (high : Bool) : 0 < criticalRatio high := by
  cases high <;> simp only [criticalRatio, Bool.false_eq_true, ↓reduceIte] <;> positivity

theorem criticalRatio_not_mul (high : Bool) :
    criticalRatio (!high) * criticalRatio high = 1 := by
  cases high <;> simp only [criticalRatio, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte]
  all_goals
    calc
      _ = Real.sqrt 2 ^ 2 / 2 := by ring
      _ = 1 := by norm_num [Real.sq_sqrt]

theorem criticalRatio_relation (high : Bool) (x : ℝ) :
    criticalRatio high * x = Real.sqrt 2 * x ∨
      x = Real.sqrt 2 * (criticalRatio high * x) := by
  cases high
  · right
    simp only [criticalRatio, Bool.false_eq_true, ↓reduceIte]
    have hq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    linear_combination -(x / 2) * hq
  · exact Or.inl rfl

/-- Every coordinate pair can be rounded to a critical ratio at squared cost
at most twice its distance-ratio error. -/
theorem exists_criticalRatio_near (x y : ℝ) :
    ∃ high : Bool, (y - criticalRatio high * x) ^ 2 ≤
      2 * edgeRatioError (Real.sqrt 2 / 2) x y := by
  have hq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  by_cases h : (y - Real.sqrt 2 / 2 * x) ^ 2 ≤ (x - Real.sqrt 2 / 2 * y) ^ 2
  · refine ⟨false, ?_⟩
    simp only [criticalRatio, Bool.false_eq_true, ↓reduceIte, edgeRatioError, min_eq_right h]
    nlinarith [sq_nonneg (y - Real.sqrt 2 / 2 * x)]
  · refine ⟨true, ?_⟩
    simp only [criticalRatio, ↓reduceIte, edgeRatioError, min_eq_left (le_of_not_ge h)]
    apply le_of_eq
    linear_combination (x ^ 2 - y ^ 2 / 2) * hq

/-- An unoriented critical ratio can be represented by a high/low flag. -/
theorem exists_criticalRatio {x y : ℝ}
    (h : y = Real.sqrt 2 * x ∨ x = Real.sqrt 2 * y) :
    ∃ high, y = criticalRatio high * x := by
  rcases h with h | h
  · exact ⟨true, by simpa [criticalRatio] using h⟩
  · refine ⟨false, ?_⟩
    simp only [criticalRatio, Bool.false_eq_true, ↓reduceIte]
    rw [h]
    ring_nf
    norm_num [Real.sq_sqrt]
    ring

/-- A saturated cubic star has exactly one high neighbor at each positive coordinate. -/
theorem one_high_of_criticalRatio_sum {x : ℝ} (hx : 0 < x) (a b c : Bool)
    (h : criticalRatio a * x + criticalRatio b * x + criticalRatio c * x =
      2 * Real.sqrt 2 * x) :
    (a = true ∧ b = false ∧ c = false) ∨
      (a = false ∧ b = true ∧ c = false) ∨
      (a = false ∧ b = false ∧ c = true) := by
  have hp : 0 < Real.sqrt 2 * x := mul_pos (by positivity) hx
  cases a <;> cases b <;> cases c <;> simp [criticalRatio] at h ⊢ <;> nlinarith

/-- A nonsaturated critical-ratio star has a fixed squared gap. This makes the
exceptional coordinate mass controllable without depending on the dimension. -/
theorem criticalRatio_sum_gap (a b c : Bool) (x : ℝ)
    (h : criticalRatio a * x + criticalRatio b * x + criticalRatio c * x ≠
      2 * Real.sqrt 2 * x) :
    x ^ 2 ≤ 2 * (criticalRatio a * x + criticalRatio b * x +
      criticalRatio c * x - 2 * Real.sqrt 2 * x) ^ 2 := by
  cases a <;> cases b <;> cases c <;>
    simp [criticalRatio] at h ⊢ <;>
    ring_nf at h <;> (try simp only [not_true_eq_false] at h) <;>
    ring_nf <;> norm_num [Real.sq_sqrt] <;>
    nlinarith [sq_nonneg x]

theorem criticalRatio_sq_bounds (high : Bool) (x : ℝ) :
    x ^ 2 / 2 ≤ (criticalRatio high * x) ^ 2 ∧
      (criticalRatio high * x) ^ 2 ≤ 2 * x ^ 2 := by
  cases high <;> constructor <;>
    norm_num [criticalRatio, mul_pow, div_pow, Real.sq_sqrt] <;>
    nlinarith [sq_nonneg x]

theorem sq_bounds_of_criticalRatio {x y : ℝ}
    (h : y = Real.sqrt 2 * x ∨ x = Real.sqrt 2 * y) :
    x ^ 2 / 2 ≤ y ^ 2 ∧ y ^ 2 ≤ 2 * x ^ 2 := by
  obtain ⟨high, rfl⟩ := exists_criticalRatio h
  exact criticalRatio_sq_bounds high x

/-- The six rows are the two centers, two left neighbors, and two right neighbors.
Each column is scaled so that its first center has value one. -/
noncomputable def criticalStarAmplitude : Fin 6 → Fin 4 → ℝ :=
  ![![1, 1, 1, 1],
    ![Real.sqrt 2 / 2, Real.sqrt 2 / 2, Real.sqrt 2, Real.sqrt 2],
    ![Real.sqrt 2, Real.sqrt 2 / 2, Real.sqrt 2 / 2, Real.sqrt 2 / 2],
    ![Real.sqrt 2 / 2, Real.sqrt 2, Real.sqrt 2 / 2, Real.sqrt 2 / 2],
    ![1 / 2, 1 / 2, 2, 1],
    ![1 / 2, 1 / 2, 1, 2]]

/-- The critical edge ratios and two star identities force one of four branch shapes. -/
theorem exists_criticalStarAmplitude (x : Fin 6 → ℝ) (hx : 0 ≤ x 0)
    (h₀₁ : x 1 = Real.sqrt 2 * x 0 ∨ x 0 = Real.sqrt 2 * x 1)
    (h₀₂ : x 2 = Real.sqrt 2 * x 0 ∨ x 0 = Real.sqrt 2 * x 2)
    (h₀₃ : x 3 = Real.sqrt 2 * x 0 ∨ x 0 = Real.sqrt 2 * x 3)
    (h₁₄ : x 4 = Real.sqrt 2 * x 1 ∨ x 1 = Real.sqrt 2 * x 4)
    (h₁₅ : x 5 = Real.sqrt 2 * x 1 ∨ x 1 = Real.sqrt 2 * x 5)
    (hleft : x 1 + x 2 + x 3 = 2 * Real.sqrt 2 * x 0)
    (hright : x 0 + x 4 + x 5 = 2 * Real.sqrt 2 * x 1) :
    ∃ b : Fin 4, ∀ i, x i = criticalStarAmplitude i b * x 0 := by
  obtain ⟨e, he⟩ := exists_criticalRatio h₀₁
  obtain ⟨a, ha⟩ := exists_criticalRatio h₀₂
  obtain ⟨b, hb⟩ := exists_criticalRatio h₀₃
  obtain ⟨c, hc⟩ := exists_criticalRatio h₁₄
  obtain ⟨d, hd⟩ := exists_criticalRatio h₁₅
  rcases eq_or_lt_of_le hx with hx | hx
  · have h₀ : x 0 = 0 := hx.symm
    have h₁ : x 1 = 0 := by rw [he, h₀, mul_zero]
    have h₂ : x 2 = 0 := by rw [ha, h₀, mul_zero]
    have h₃ : x 3 = 0 := by rw [hb, h₀, mul_zero]
    have h₄ : x 4 = 0 := by rw [hc, h₁, mul_zero]
    have h₅ : x 5 = 0 := by rw [hd, h₁, mul_zero]
    have hzero : ∀ i, x i = 0 := by
      intro i
      fin_cases i <;> assumption
    exact ⟨0, fun i => by simp [hzero]⟩
  have hv : 0 < x 1 := by rw [he]; exact mul_pos (criticalRatio_pos e) hx
  have hrev : x 0 = criticalRatio (!e) * x 1 := by
    rw [he, ← mul_assoc, criticalRatio_not_mul, one_mul]
  have hl := one_high_of_criticalRatio_sum hx e a b (by simpa only [← he, ← ha, ← hb] using hleft)
  have hr := one_high_of_criticalRatio_sum hv (!e) c d
    (by simpa only [← hrev, ← hc, ← hd] using hright)
  clear hrev h₀₁ h₀₂ h₀₃ h₁₄ h₁₅ hleft hright
  refine ⟨if a then 0 else if b then 1 else if c then 2 else 3, ?_⟩
  intro i
  cases e <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false,
      and_true, and_false, or_true, or_false,
      ↓reduceIte] at hl hr ⊢ <;>
    fin_cases i <;>
    simp [criticalStarAmplitude, criticalRatio, he, ha, hb, hc, hd] <;>
    ring_nf <;> norm_num [Real.sq_sqrt] <;> ring

/-- The five edge-ratio constraints for two adjacent cubic stars. -/
def CriticalStarRatios (x : Fin 6 → ℝ) : Prop :=
  (x 1 = Real.sqrt 2 * x 0 ∨ x 0 = Real.sqrt 2 * x 1) ∧
  (x 2 = Real.sqrt 2 * x 0 ∨ x 0 = Real.sqrt 2 * x 2) ∧
  (x 3 = Real.sqrt 2 * x 0 ∨ x 0 = Real.sqrt 2 * x 3) ∧
  (x 4 = Real.sqrt 2 * x 1 ∨ x 1 = Real.sqrt 2 * x 4) ∧
  (x 5 = Real.sqrt 2 * x 1 ∨ x 1 = Real.sqrt 2 * x 5)

/-- Total distance from the critical ratios on the five edges of the two stars. -/
noncomputable def criticalStarRatioDefect (x : Fin 6 → ℝ) : ℝ :=
  edgeRatioError (Real.sqrt 2 / 2) (x 0) (x 1) +
    edgeRatioError (Real.sqrt 2 / 2) (x 0) (x 2) +
    edgeRatioError (Real.sqrt 2 / 2) (x 0) (x 3) +
    edgeRatioError (Real.sqrt 2 / 2) (x 1) (x 4) +
    edgeRatioError (Real.sqrt 2 / 2) (x 1) (x 5)

theorem criticalStarRatioDefect_nonneg (x : Fin 6 → ℝ) : 0 ≤ criticalStarRatioDefect x := by
  unfold criticalStarRatioDefect edgeRatioError
  positivity

/-- The five ratios can be rounded jointly while keeping the first center
fixed. The two stars share one center coordinate in this construction. -/
theorem exists_criticalStarRatios_near (x : Fin 6 → ℝ) :
    ∃ y : Fin 6 → ℝ, y 0 = x 0 ∧ CriticalStarRatios y ∧
      ∀ i, (x i - y i) ^ 2 ≤ 12 * criticalStarRatioDefect x := by
  obtain ⟨e, he⟩ := exists_criticalRatio_near (x 0) (x 1)
  obtain ⟨a, ha⟩ := exists_criticalRatio_near (x 0) (x 2)
  obtain ⟨b, hb⟩ := exists_criticalRatio_near (x 0) (x 3)
  obtain ⟨c, hc⟩ := exists_criticalRatio_near (x 1) (x 4)
  obtain ⟨d, hd⟩ := exists_criticalRatio_near (x 1) (x 5)
  let y := ![x 0, criticalRatio e * x 0, criticalRatio a * x 0,
    criticalRatio b * x 0, criticalRatio c * (criticalRatio e * x 0),
    criticalRatio d * (criticalRatio e * x 0)]
  have hn₁ := edgeRatioError_nonneg (Real.sqrt 2 / 2) (x 0) (x 1)
  have hn₂ := edgeRatioError_nonneg (Real.sqrt 2 / 2) (x 0) (x 2)
  have hn₃ := edgeRatioError_nonneg (Real.sqrt 2 / 2) (x 0) (x 3)
  have hn₄ := edgeRatioError_nonneg (Real.sqrt 2 / 2) (x 1) (x 4)
  have hn₅ := edgeRatioError_nonneg (Real.sqrt 2 / 2) (x 1) (x 5)
  have hbase : (x 1 - criticalRatio e * x 0) ^ 2 ≤ 2 * criticalStarRatioDefect x := by
    unfold criticalStarRatioDefect
    linarith
  have hleft : (x 4 - criticalRatio c * (criticalRatio e * x 0)) ^ 2 ≤
      12 * criticalStarRatioDefect x := by
    have hr := (criticalRatio_sq_bounds c (x 1 - criticalRatio e * x 0)).2
    have houter : (x 4 - criticalRatio c * x 1) ^ 2 ≤ 2 * criticalStarRatioDefect x := by
      unfold criticalStarRatioDefect
      linarith
    nlinarith only [hbase, houter, hr,
      sq_nonneg ((x 4 - criticalRatio c * x 1) - criticalRatio c *
        (x 1 - criticalRatio e * x 0))]
  have hright : (x 5 - criticalRatio d * (criticalRatio e * x 0)) ^ 2 ≤
      12 * criticalStarRatioDefect x := by
    have hr := (criticalRatio_sq_bounds d (x 1 - criticalRatio e * x 0)).2
    have houter : (x 5 - criticalRatio d * x 1) ^ 2 ≤ 2 * criticalStarRatioDefect x := by
      unfold criticalStarRatioDefect
      linarith
    nlinarith only [hbase, houter, hr,
      sq_nonneg ((x 5 - criticalRatio d * x 1) - criticalRatio d *
        (x 1 - criticalRatio e * x 0))]
  refine ⟨y, rfl, ?_, ?_⟩
  · exact ⟨criticalRatio_relation e _, criticalRatio_relation a _, criticalRatio_relation b _,
      criticalRatio_relation c _, criticalRatio_relation d _⟩
  · intro i
    fin_cases i
    · change (x 0 - x 0) ^ 2 ≤ 12 * criticalStarRatioDefect x
      nlinarith [criticalStarRatioDefect_nonneg x]
    · change (x 1 - criticalRatio e * x 0) ^ 2 ≤ 12 * criticalStarRatioDefect x
      linarith [criticalStarRatioDefect_nonneg x]
    · change (x 2 - criticalRatio a * x 0) ^ 2 ≤ 12 * criticalStarRatioDefect x
      unfold criticalStarRatioDefect
      linarith
    · change (x 3 - criticalRatio b * x 0) ^ 2 ≤ 12 * criticalStarRatioDefect x
      unfold criticalStarRatioDefect
      linarith
    · exact hleft
    · exact hright

/-- Joint coordinate rounding gives exact critical-ratio rows with an explicit
squared-distance bound, uniform in the number of coordinates. -/
theorem exists_criticalStarRows_near {ι : Type*} [Fintype ι] (x : Fin 6 → ι → ℝ) :
    ∃ y : Fin 6 → ι → ℝ, (∀ k, y 0 k = x 0 k) ∧
      (∀ k, CriticalStarRatios (fun i => y i k)) ∧
      ∀ i, (∑ k, (x i k - y i k) ^ 2) ≤
        12 * ∑ k, criticalStarRatioDefect (fun i => x i k) := by
  classical
  choose y hy₀ hy hyerr using fun k => exists_criticalStarRatios_near (fun i => x i k)
  refine ⟨fun i k => y k i, hy₀, hy, ?_⟩
  intro i
  simpa only [← mul_sum] using sum_le_sum fun k (_ : k ∈ univ) => hyerr k i

/-- Squared error in the two saturated star equations. -/
noncomputable def criticalStarDefect (x : Fin 6 → ℝ) : ℝ :=
  (x 1 + x 2 + x 3 - 2 * Real.sqrt 2 * x 0) ^ 2 +
    (x 0 + x 4 + x 5 - 2 * Real.sqrt 2 * x 1) ^ 2

theorem criticalStarDefect_nonneg (x : Fin 6 → ℝ) : 0 ≤ criticalStarDefect x := by
  unfold criticalStarDefect
  positivity

/-- Each row coordinate has squared size at most four times the first center. -/
theorem CriticalStarRatios.sq_le {x : Fin 6 → ℝ} (h : CriticalStarRatios x) (i : Fin 6) :
    x i ^ 2 ≤ 4 * x 0 ^ 2 := by
  have h₁ := sq_bounds_of_criticalRatio h.1
  have h₂ := sq_bounds_of_criticalRatio h.2.1
  have h₃ := sq_bounds_of_criticalRatio h.2.2.1
  have h₄ := sq_bounds_of_criticalRatio h.2.2.2.1
  have h₅ := sq_bounds_of_criticalRatio h.2.2.2.2
  fin_cases i <;> dsimp <;> nlinarith [sq_nonneg (x 0)]

/-- Coordinates not belonging to a saturated branch have controlled mass.
This is a quantitative statement; no exact star equation is assumed. -/
theorem CriticalStarRatios.mass_le_defect {x : Fin 6 → ℝ} (h : CriticalStarRatios x)
    (hx : 0 ≤ x 0)
    (hbad : ¬ ∃ b : Fin 4, ∀ i, x i = criticalStarAmplitude i b * x 0) :
    x 0 ^ 2 ≤ 4 * criticalStarDefect x := by
  obtain ⟨e, he⟩ := exists_criticalRatio h.1
  obtain ⟨a, ha⟩ := exists_criticalRatio h.2.1
  obtain ⟨b, hb⟩ := exists_criticalRatio h.2.2.1
  obtain ⟨c, hc⟩ := exists_criticalRatio h.2.2.2.1
  obtain ⟨d, hd⟩ := exists_criticalRatio h.2.2.2.2
  have hrev : x 0 = criticalRatio (!e) * x 1 := by
    rw [he, ← mul_assoc, criticalRatio_not_mul, one_mul]
  by_cases hl : x 1 + x 2 + x 3 = 2 * Real.sqrt 2 * x 0
  · have hr : x 0 + x 4 + x 5 ≠ 2 * Real.sqrt 2 * x 1 := by
      intro hr
      exact hbad (exists_criticalStarAmplitude x hx h.1 h.2.1 h.2.2.1
        h.2.2.2.1 h.2.2.2.2 hl hr)
    have hg := criticalRatio_sum_gap (!e) c d (x 1)
      (by simpa only [← hrev, ← hc, ← hd] using hr)
    rw [← hrev, ← hc, ← hd] at hg
    have hsq := (sq_bounds_of_criticalRatio h.1).1
    unfold criticalStarDefect
    nlinarith [sq_nonneg (x 1 + x 2 + x 3 - 2 * Real.sqrt 2 * x 0)]
  · have hg := criticalRatio_sum_gap e a b (x 0)
      (by simpa only [← he, ← ha, ← hb] using hl)
    rw [← he, ← ha, ← hb] at hg
    unfold criticalStarDefect
    nlinarith [sq_nonneg (x 0 + x 4 + x 5 - 2 * Real.sqrt 2 * x 1), sq_nonneg (x 0)]

/-- The variance of a row in a weighted mixture of the four branch shapes. -/
noncomputable def criticalStarVariance (w : Fin 4 → ℝ) (i : Fin 6) : ℝ :=
  ∑ b, w b * criticalStarAmplitude i b ^ 2

/-- Inversion of the four independent variance equations. It also supplies
quantitative stability when the row variances are only close to one. -/
theorem criticalStarWeights_eq_variances (w : Fin 4 → ℝ) :
    w = ![(2 * criticalStarVariance w 2 - criticalStarVariance w 0) / 3,
      (5 * criticalStarVariance w 0 - 2 * criticalStarVariance w 1 -
        2 * criticalStarVariance w 2) / 3,
      (2 * criticalStarVariance w 4 - criticalStarVariance w 1) / 6,
      (5 * criticalStarVariance w 1 - 2 * criticalStarVariance w 0 -
        2 * criticalStarVariance w 4) / 6] := by
  ext b
  fin_cases b <;>
    norm_num [criticalStarVariance, criticalStarAmplitude, Fin.sum_univ_succ,
      div_pow, Real.sq_sqrt] <;> ring

/-- Unit variances force exactly the symmetric cubic-tree weights. -/
theorem criticalStarWeights_eq_of_unit (w : Fin 4 → ℝ)
    (h : ∀ i, criticalStarVariance w i = 1) :
    w = ![1 / 3, 1 / 3, 1 / 6, 1 / 6] := by
  rw [criticalStarWeights_eq_variances w]
  norm_num [h]

/-- Stability of the four branch weights under an error bound on row variances. -/
theorem criticalStarWeights_stable (w : Fin 4 → ℝ) {ε : ℝ}
    (h : ∀ i, |criticalStarVariance w i - 1| ≤ ε) :
    |w 0 - 1 / 3| ≤ ε ∧ |w 1 - 1 / 3| ≤ 3 * ε ∧
      |w 2 - 1 / 6| ≤ ε / 2 ∧ |w 3 - 1 / 6| ≤ 3 * ε / 2 := by
  have h₀ := abs_le.mp (h 0)
  have h₁ := abs_le.mp (h 1)
  have h₂ := abs_le.mp (h 2)
  have h₄ := abs_le.mp (h 4)
  have heq := congrFun (criticalStarWeights_eq_variances w)
  have hw₀ := heq 0
  have hw₁ := heq 1
  have hw₂ := heq 2
  have hw₃ := heq 3
  norm_num only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    at hw₀ hw₁ hw₂ hw₃
  rw [hw₀, hw₁, hw₂, hw₃]
  simp only [abs_le]
  constructor
  · constructor <;> linarith
  · constructor
    · constructor <;> linarith
    · constructor <;> constructor <;> linarith

/-- Grouping coordinates by their branch shape gives a nonnegative mixture.
The same four weights determine every inner product, not just the variances. -/
theorem exists_criticalStarWeights {ι : Type*} [Fintype ι]
    (x : Fin 6 → ι → ℝ)
    (hshape : ∀ k, ∃ b : Fin 4, ∀ i,
      x i k = criticalStarAmplitude i b * x 0 k) :
    ∃ w : Fin 4 → ℝ, (∀ b, 0 ≤ w b) ∧
      ∀ i j, ∑ k, x i k * x j k =
        ∑ b, w b * criticalStarAmplitude i b * criticalStarAmplitude j b := by
  classical
  choose branch hbranch using hshape
  let w := fun b => ∑ k with branch k = b, x 0 k ^ 2
  refine ⟨w, fun b => sum_nonneg fun k _ => sq_nonneg _, ?_⟩
  intro i j
  calc
    ∑ k, x i k * x j k =
        ∑ b : Fin 4, ∑ k with branch k = b, x i k * x j k := by
      symm
      simpa using sum_fiberwise_eq_sum_filter univ univ branch
        (fun k => x i k * x j k)
    _ = ∑ b, w b * criticalStarAmplitude i b * criticalStarAmplitude j b := by
      apply sum_congr rfl
      intro b _
      simp only [w, sum_mul]
      apply sum_congr rfl
      intro k hk
      have hb := (mem_filter.mp hk).2
      rw [hbranch k i, hbranch k j, hb]
      ring

/-- The covariance of the six unit rows in the saturated two-star model. -/
noncomputable def criticalStarGram : Fin 6 → Fin 6 → ℝ :=
  let ρ := 2 * Real.sqrt 2 / 3
  let d := Real.sqrt 2 / 2
  ![![1, ρ, ρ, ρ, 5 / 6, 5 / 6],
    ![ρ, 1, 5 / 6, 5 / 6, ρ, ρ],
    ![ρ, 5 / 6, 1, 5 / 6, d, d],
    ![ρ, 5 / 6, 5 / 6, 1, d, d],
    ![5 / 6, ρ, d, d, 1, 5 / 6],
    ![5 / 6, ρ, d, d, 5 / 6, 1]]

theorem criticalStarGram_eq_mixture (i j : Fin 6) :
    criticalStarGram i j = ∑ b : Fin 4,
      ![(1 : ℝ) / 3, 1 / 3, 1 / 6, 1 / 6] b *
        criticalStarAmplitude i b * criticalStarAmplitude j b := by
  fin_cases i <;> fin_cases j <;>
    norm_num [criticalStarGram, criticalStarAmplitude, Fin.sum_univ_succ] <;>
    ring_nf <;> norm_num [Real.sq_sqrt]

/-- Unit variances turn pointwise branch rigidity into the full joint covariance. -/
theorem sum_mul_eq_criticalStarGram {ι : Type*} [Fintype ι]
    (x : Fin 6 → ι → ℝ)
    (hshape : ∀ k, ∃ b : Fin 4, ∀ i,
      x i k = criticalStarAmplitude i b * x 0 k)
    (hunit : ∀ i, ∑ k, x i k ^ 2 = 1) (i j : Fin 6) :
    ∑ k, x i k * x j k = criticalStarGram i j := by
  obtain ⟨w, _, hw⟩ := exists_criticalStarWeights x hshape
  have hv : ∀ i, criticalStarVariance w i = 1 := by
    intro i
    have hi := hw i i
    simpa only [criticalStarVariance, mul_assoc, ← sq, hunit] using hi.symm
  rw [hw, criticalStarWeights_eq_of_unit w hv, criticalStarGram_eq_mixture]

theorem abs_criticalStarAmplitude_le (i : Fin 6) (b : Fin 4) :
    |criticalStarAmplitude i b| ≤ 2 := by
  have hq : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_left (by norm_num)).mpr (by norm_num)
  fin_cases i <;> fin_cases b <;>
    norm_num [criticalStarAmplitude, abs_div, abs_of_nonneg (Real.sqrt_nonneg 2)] <;>
    linarith

/-- Variance errors control every covariance of a branch mixture, uniformly in
the number of underlying Gaussian coordinates. -/
theorem criticalStarMixture_stable (w : Fin 4 → ℝ) {ε : ℝ}
    (h : ∀ i, |criticalStarVariance w i - 1| ≤ ε) (i j : Fin 6) :
    |(∑ b, w b * criticalStarAmplitude i b * criticalStarAmplitude j b) -
      criticalStarGram i j| ≤ 24 * ε := by
  let w₀ : Fin 4 → ℝ := ![1 / 3, 1 / 3, 1 / 6, 1 / 6]
  have hw := criticalStarWeights_stable w h
  have hsum : (∑ b, |w b - w₀ b|) ≤ 6 * ε := by
    norm_num [w₀, Fin.sum_univ_succ]
    linarith [hw.1, hw.2.1, hw.2.2.1, hw.2.2.2]
  have heq : (∑ b, w b * criticalStarAmplitude i b * criticalStarAmplitude j b) -
      criticalStarGram i j =
      ∑ b, (w b - w₀ b) * criticalStarAmplitude i b * criticalStarAmplitude j b := by
    rw [criticalStarGram_eq_mixture, ← sum_sub_distrib]
    apply sum_congr rfl
    intro b _
    dsimp [w₀]
    ring
  rw [heq]
  calc
    _ ≤ ∑ b, |(w b - w₀ b) * criticalStarAmplitude i b * criticalStarAmplitude j b| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, |w b - w₀ b| * 4 := by
      apply sum_le_sum
      intro b _
      rw [abs_mul, abs_mul, mul_assoc]
      have hp : |criticalStarAmplitude i b| * |criticalStarAmplitude j b| ≤ 4 := by
        calc
          _ ≤ 2 * |criticalStarAmplitude j b| :=
            mul_le_mul_of_nonneg_right (abs_criticalStarAmplitude_le i b) (abs_nonneg _)
          _ ≤ 4 := by linarith [abs_criticalStarAmplitude_le j b]
      exact mul_le_mul_of_nonneg_left hp (abs_nonneg _)
    _ ≤ 24 * ε := by rw [← sum_mul]; linarith

/-- Star residuals and variance errors control the entire Gram matrix, uniformly
in dimension. This form also applies to rows obtained by joint ratio rounding. -/
theorem criticalStarGram_stable_of_variances {ι : Type*} [Fintype ι] {ε : ℝ}
    (x : Fin 6 → ι → ℝ) (hx : ∀ k, 0 ≤ x 0 k)
    (hratio : ∀ k, CriticalStarRatios (fun i => x i k))
    (hvar : ∀ i, |(∑ k, x i k ^ 2) - 1| ≤ ε) (i j : Fin 6) :
    |(∑ k, x i k * x j k) - criticalStarGram i j| ≤
      400 * (∑ k, criticalStarDefect (fun i => x i k)) + 24 * ε := by
  classical
  let good := fun k => ∃ b : Fin 4, ∀ i,
    x i k = criticalStarAmplitude i b * x 0 k
  let y := fun i k => if good k then x i k else 0
  have hy : ∀ k, ∃ b : Fin 4, ∀ i,
      y i k = criticalStarAmplitude i b * y 0 k := by
    intro k
    by_cases hk : good k
    · simpa only [y, ite_eq_left hk] using hk
    · exact ⟨0, by simp [y, hk]⟩
  obtain ⟨w, _, hw⟩ := exists_criticalStarWeights y hy
  have hp (i j : Fin 6) (k : ι) :
      |x i k * x j k - y i k * y j k| ≤
        16 * criticalStarDefect (fun i => x i k) := by
    by_cases hk : good k
    · simp only [y, ite_eq_left hk, sub_self, abs_zero]
      exact mul_nonneg (by norm_num) (criticalStarDefect_nonneg _)
    · simp only [y, ite_eq_right hk, zero_mul, sub_zero]
      have hm := (hratio k).mass_le_defect (hx k) hk
      have hi := (hratio k).sq_le i
      have hj := (hratio k).sq_le j
      have hprod : |x i k * x j k| ≤ 4 * x 0 k ^ 2 := by
        rw [abs_le]
        constructor <;>
          nlinarith [sq_nonneg (x i k - x j k), sq_nonneg (x i k + x j k)]
      linarith
  have herr (i j : Fin 6) :
      |(∑ k, x i k * x j k) - ∑ k, y i k * y j k| ≤
        16 * ∑ k, criticalStarDefect (fun i => x i k) := by
    rw [← sum_sub_distrib]
    calc
      _ ≤ ∑ k, |x i k * x j k - y i k * y j k| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, 16 * criticalStarDefect (fun i => x i k) :=
        sum_le_sum fun k _ => hp i j k
      _ = _ := (mul_sum _ _ _).symm
  have hv (i : Fin 6) : |criticalStarVariance w i - 1| ≤
      16 * (∑ k, criticalStarDefect (fun i => x i k)) + ε := by
    have h := herr i i
    rw [hw] at h
    have hdiff : |criticalStarVariance w i - ∑ k, x i k ^ 2| ≤
        16 * ∑ k, criticalStarDefect (fun i => x i k) := by
      simpa only [criticalStarVariance, mul_assoc, ← sq, abs_sub_comm] using h
    exact (abs_sub_le _ (∑ k, x i k ^ 2) _).trans (add_le_add hdiff (hvar i))
  have hstable := criticalStarMixture_stable w hv i j
  rw [← hw] at hstable
  have htri := abs_sub_le (∑ k, x i k * x j k) (∑ k, y i k * y j k)
    (criticalStarGram i j)
  linarith [herr i j]

/-- Near saturation controls the entire Gram matrix of unit rows. The error is
the sum of the two squared star residuals. The five edge ratios are exact here. -/
theorem criticalStarGram_stable {ι : Type*} [Fintype ι]
    (x : Fin 6 → ι → ℝ) (hx : ∀ k, 0 ≤ x 0 k)
    (hratio : ∀ k, CriticalStarRatios (fun i => x i k))
    (hunit : ∀ i, ∑ k, x i k ^ 2 = 1) (i j : Fin 6) :
    |(∑ k, x i k * x j k) - criticalStarGram i j| ≤
      400 * ∑ k, criticalStarDefect (fun i => x i k) := by
  simpa using criticalStarGram_stable_of_variances (ε := 0) x hx hratio
    (fun i => by rw [hunit i]; norm_num) i j

/-- The four outer edge vectors of a two-star patch, normalized at the critical
adjacent correlation. The centers of ports zero and one are row zero; the other
two ports have center row one. -/
noncomputable def criticalStarPort {ι : Type*} (x : Fin 6 → ι → ℝ)
    (i : Fin 4) (k : ι) : ℝ :=
  (x (![0, 0, 1, 1] i) k + x (![2, 3, 4, 5] i) k) /
    Real.sqrt (2 + 4 * Real.sqrt 2 / 3)

/-- The outer edge covariance is exactly the covariance used by the checked
two-vertex Gaussian cost estimate. -/
theorem sum_criticalStarPort_mul {ι : Type*} [Fintype ι]
    (x : Fin 6 → ι → ℝ)
    (hgram : ∀ i j, ∑ k, x i k * x j k = criticalStarGram i j)
    (i j : Fin 4) :
    ∑ k, criticalStarPort x i k * criticalStarPort x j k =
      if i = j then 1 else
        if (i < 2 ∧ j < 2) ∨ (2 ≤ i ∧ 2 ≤ j) then (1 + 2 * Real.sqrt 2) / 4
          else (2 + Real.sqrt 2) / 4 := by
  have hden : 0 < 2 + 4 * Real.sqrt 2 / 3 := by positivity
  simp only [criticalStarPort, div_mul_div_comm, ← sq,
    Real.sq_sqrt hden.le, ← sum_div, add_mul, mul_add, sum_add_distrib, hgram]
  fin_cases i <;> fin_cases j <;> norm_num [criticalStarGram] <;>
    field_simp <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- Exact saturated stars satisfy the local Gaussian patch estimate in any
finite coordinate space. This connects ratio rigidity to the probability bound. -/
theorem integral_criticalStarPort_cost_le {ι : Type} [Fintype ι]
    (x : Fin 6 → ι → ℝ) (hx : ∀ k, 0 ≤ x 0 k)
    (hratio : ∀ k, CriticalStarRatios (fun i => x i k))
    (hleft : ∀ k, x 1 k + x 2 k + x 3 k = 2 * Real.sqrt 2 * x 0 k)
    (hright : ∀ k, x 0 k + x 4 k + x 5 k = 2 * Real.sqrt 2 * x 1 k)
    (hunit : ∀ i, ∑ k, x i k ^ 2 = 1) (t : ℝ) :
    (∫ ω, (twoVertexCost
      (belowThreshold t (form (criticalStarPort x 0) ω))
      (belowThreshold t (form (criticalStarPort x 1) ω))
      (belowThreshold t (form (criticalStarPort x 2) ω))
      (belowThreshold t (form (criticalStarPort x 3) ω)) : ℝ) ∂gaussPi ι) ≤
        twoVertexTreeBound := by
  have hshape (k : ι) := exists_criticalStarAmplitude (fun i => x i k) (hx k)
    (hratio k).1 (hratio k).2.1 (hratio k).2.2.1
    (hratio k).2.2.2.1 (hratio k).2.2.2.2 (hleft k) (hright k)
  have hcov := sum_criticalStarPort_mul x (sum_mul_eq_criticalStarGram x hshape hunit)
  apply integral_twoVertexCost_le_of_tree_gram
  · intro i
    simpa only [← sq, ite_true] using hcov i i
  · intro i j hij
    rw [hcov]
    fin_cases i <;> fin_cases j <;> norm_num at hij <;> norm_num

end Frontier.Gaussian
