/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Arithmetic.DeterminantPolynomial
public import Frontier.Arithmetic.DeterminantMatching
public import Frontier.Arithmetic.LowerBound
public import Frontier.Boundary.Fiber
import Mathlib.Tactic

/-! # Determinant demand and arithmetic circuit lower bounds -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Frontier.Arithmetic

open MvPolynomial Matrix Finset DeterminantMatching

variable {F : Type*} [Field F] {n : ℕ}

/-- Each split matching edge gives a nonzero diagonal entry in a Hessian submatrix. -/
theorem crossing_le_mixedRank (S : Finset (Fin n × Fin n)) (π : Equiv.Perm (Fin n)) :
    crossing S π ≤ mixedRank (determinant F n) (permutationPoint π)
      {c | finProdFinEquiv.symm c ∈ S} := by
  classical
  let C := {p : Pair (Fin n) // (p.1.1, π p.1.2) ∈ S ∧ (p.1.2, π p.1.1) ∉ S}
  let rows : C → {c : Fin (n * n) | finProdFinEquiv.symm c ∈ S} := fun p =>
    ⟨finProdFinEquiv (p.1.1.1, π p.1.1.2), by
      simpa only [Set.mem_ofPred_eq, Equiv.symm_apply_apply] using p.2.1⟩
  let cols : C → {c : Fin (n * n) | finProdFinEquiv.symm c ∉ S} := fun p =>
    ⟨finProdFinEquiv (p.1.1.2, π p.1.1.1), by
      simpa only [Set.mem_ofPred_eq, Equiv.symm_apply_apply] using p.2.2⟩
  let M := mixedHessian (determinant F n) (permutationPoint π)
    {c | finProdFinEquiv.symm c ∈ S}
  have hM : M.submatrix rows cols = diagonal (fun _ : C => -(π.sign : F)) := by
    ext p q
    change hessian (determinant F n) (permutationPoint π)
      (finProdFinEquiv (p.1.1.1, π p.1.1.2))
      (finProdFinEquiv (q.1.1.2, π q.1.1.1)) = _
    rw [hessian_determinant_permutation π _ _ _ _ p.1.2, diagonal_apply]
    have he : (p.1.1.1 = q.1.1.1 ∧ p.1.1.2 = q.1.1.2) ↔ p = q := by
      constructor
      · rintro ⟨h₁, h₂⟩
        exact Subtype.ext (Subtype.ext (Prod.ext h₁ h₂))
      · rintro rfl
        exact ⟨rfl, rfl⟩
    simp only [he]
  have hcard : crossing S π = Fintype.card C := by
    simp [crossing, C, Fintype.card_subtype]
  rw [hcard, mixedRank_eq]
  have hle := Matrix.rank_submatrix_le M rows cols
  rw [hM, rank_diagonal] at hle
  simpa [sign_cast_ne_zero (F := F) π] using hle

/-- A balanced entry partition has determinant mixed rank `n²/4 - 3n` at some permutation. -/
theorem determinant_balanced_rank (S : Finset (Fin n × Fin n))
    (hS : S.card = n * n / 2) :
    ∃ π : Equiv.Perm (Fin n), (n : ℝ)^2 / 4 - 3 * n ≤
      (mixedRank (determinant F n) (permutationPoint π)
        {c | finProdFinEquiv.symm c ∈ S} : ℝ) := by
  classical
  obtain ⟨π, hπ⟩ := exists_crossing S
  have hc := S.card_add_card_compl
  simp only [Fintype.card_prod, Fintype.card_fin] at hc hπ
  have hb : S.card ≤ Sᶜ.card ∧ Sᶜ.card ≤ S.card + 1 := by lia
  have hcard : (S.card : ℝ) + Sᶜ.card = (n : ℝ)^2 := by
    rw [pow_two]
    exact_mod_cast hc
  have hb₁ : (S.card : ℝ) ≤ Sᶜ.card := by exact_mod_cast hb.1
  have hb₂ : (Sᶜ.card : ℝ) ≤ S.card + 1 := by exact_mod_cast hb.2
  have hp : (n : ℝ)^4 - 1 ≤ 4 * (S.card : ℝ) * Sᶜ.card := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb₁) (sub_nonneg.mpr hb₂)]
  have hπ' : (S.card : ℝ) * Sᶜ.card ≤
      (n : ℝ)^2 * crossing S π + 2 * (n : ℝ)^3 := by exact_mod_cast hπ
  have hr : (crossing S π : ℝ) ≤ mixedRank (determinant F n) (permutationPoint π)
      {c | finProdFinEquiv.symm c ∈ S} := by exact_mod_cast crossing_le_mixedRank (F := F) S π
  refine ⟨π, le_trans ?_ hr⟩
  by_cases hn : n = 0
  · simp [hn]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by lia)
  have hn2 : (0 : ℝ) < (n : ℝ)^2 := by positivity
  apply (mul_le_mul_iff_right₀ hn2).mp
  nlinarith [sq_nonneg ((n : ℝ) - 1), mul_nonneg (sub_nonneg.mpr hn')
    (sq_nonneg (n : ℝ))]

/-- Every injective order of finitely many inputs has a prefix of any prescribed size. -/
theorem exists_prefix_card {N k : ℕ} (pos : Fin N ↪ ℕ) (hk : k ≤ N) :
    ∃ t : ℕ, (Finset.univ.filter (fun i => pos i < t)).card = k := by
  classical
  let T := Finset.univ.sup pos + 1
  have hfull : Finset.univ.filter (fun i => pos i < T) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i hi
    exact Nat.lt_succ_of_le (Finset.le_sup hi)
  have hstep (t : ℕ) : (Finset.univ.filter (fun i => pos i < t + 1)).card ≤
      (Finset.univ.filter (fun i => pos i < t)).card + 1 := by
    have he : Finset.univ.filter (fun i => pos i < t + 1) =
        Finset.univ.filter (fun i => pos i < t) ∪
          Finset.univ.filter (fun i => pos i = t) := by
      ext i
      simp only [mem_filter, mem_univ, true_and, mem_union]
      lia
    have hsingle : (Finset.univ.filter (fun i => pos i = t)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      exact pos.injective ((mem_filter.mp hi).2.trans (mem_filter.mp hj).2.symm)
    rw [he]
    exact (card_union_le _ _).trans (Nat.add_le_add_left hsingle _)
  obtain ⟨t, _, ht⟩ := Frontier.exists_eq_of_le_succ
    (a := fun t => (Finset.univ.filter (fun i => pos i < t)).card)
    (by simp) (T := T) (by simpa [hfull] using hk) (fun t _ => hstep t)
  exact ⟨t, ht⟩

/-- **Determinant demand:** every input order has mixed rank at least `n²/4 - 3n`.
The evaluation point is a permutation matrix and may depend on the input order. -/
theorem hessianDemand_determinant :
    HessianDemand (determinant F n) ((n : ℝ)^2 / 4 - 3 * n) := by
  classical
  intro pos
  obtain ⟨t, ht⟩ := exists_prefix_card pos (Nat.div_le_self (n * n) 2)
  let S := (Finset.univ.filter (fun i => pos i < t)).map finProdFinEquiv.symm.toEmbedding
  have hS : S.card = n * n / 2 := by simpa [S] using ht
  obtain ⟨π, hπ⟩ := determinant_balanced_rank (F := F) S hS
  have he : {c | finProdFinEquiv.symm c ∈ S} = {c | pos c < t} := by
    ext c
    simp only [S, Set.mem_ofPred_eq, Finset.mem_map_equiv, Equiv.symm_symm,
      Equiv.apply_symm_apply, mem_filter, mem_univ, true_and]
  rw [he] at hπ
  exact ⟨t, permutationPoint π, hπ⟩

open Cslib.Circuits Filter

universe u v

/-- **Finite determinant lower bound**, with free constants and arbitrary fan-in-two
polynomial operations. Computation means equality of formal polynomials. -/
theorem determinant_gate_bound {A η : ℝ} (hA : 0 ≤ A) (hlayout : LayoutBound 3 A)
    (hη : 0 < η) : ∃ C : ℝ, ∀ (F : Type u) [Field F] (σ : Signature.{v})
      (P : (o : σ.Op) → MvPolynomial (Fin (σ.Arity o)) F)
      (n s : ℕ) (p : Program σ (n * n) s) (out : Unit → Wire (n * n) s),
      2 ≤ n → p.FanInAtMost 2 → wirePolynomial P p (out ()) = determinant F n →
      (A + η) * (n : ℝ)^2 + (n : ℝ)^2 / 4 - 3 * n ≤
        (A + 5 * η) * p.innerGates.card + A + 4 * η + C := by
  obtain ⟨C, hC⟩ := hessian_gate_bound.{u, v} hA hlayout hη
  refine ⟨C, ?_⟩
  intro F _ σ P n s p out hn hfan hdet
  have hvars : ∀ i, i ∈ (wirePolynomial P p (out ())).vars := by
    rw [hdet]
    exact mem_vars_determinant hn
  have hd : HessianDemand (wirePolynomial P p (out ())) ((n : ℝ)^2 / 4 - 3 * n) := by
    rw [hdet]
    exact hessianDemand_determinant
  simpa only [Nat.cast_mul, pow_two, add_sub_assoc] using
    hC F σ P (n * n) s p out _ hfan hvars hd

/-- **Asymptotic determinant lower bound** from any subcubic layout coefficient.
The threshold is uniform over fields and polynomial gate bases. -/
theorem lowerBound_determinant {A : ℝ} (hA : 0 < A) (hlayout : LayoutBound 3 A)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (F : Type u) [Field F] (σ : Signature.{v})
      (P : (o : σ.Op) → MvPolynomial (Fin (σ.Arity o)) F)
      (s : ℕ) (p : Program σ (n * n) s) (out : Unit → Wire (n * n) s),
      p.FanInAtMost 2 → wirePolynomial P p (out ()) = determinant F n →
      (1 + 1 / (4 * A) - ε) * (n : ℝ)^2 < p.innerGates.card := by
  let K := 1 + 1 / (4 * A)
  have hK : 0 < K := by dsimp [K]; positivity
  have hKA : A * K = A + 1 / 4 := by dsimp [K]; field_simp
  let η := ε * A / (10 * (K + 1))
  have hη : 0 < η := by positivity
  have hηeq : 10 * (K + 1) * η = ε * A := by dsimp [η]; field_simp
  let δ := A + η + 1 / 4 - (A + 5 * η) * (K - ε)
  have hδ : 0 < δ := by dsimp [δ]; nlinarith
  obtain ⟨C, hC⟩ := determinant_gate_bound.{u, v} hA.le hlayout hη
  let B := max (A + 4 * η + C) 0
  have hB : 0 ≤ B := le_max_right _ _
  have hlarge : ∀ᶠ n : ℕ in atTop, (B + 3) / δ < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
  filter_upwards [hlarge, eventually_ge_atTop 2] with n hn hn2
  intro F _ σ P s p out hfan hdet
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by lia)
  have hnpos : (0 : ℝ) < n := by linarith
  have hlin : B + 3 < δ * n := by
    simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hn
  have hconst : 3 * (n : ℝ) + A + 4 * η + C < δ * (n : ℝ)^2 := by
    have hb : A + 4 * η + C ≤ B * n :=
      (le_max_left _ _).trans (le_mul_of_one_le_right hB hn1)
    have hm := mul_lt_mul_of_pos_right hlin hnpos
    nlinarith
  have hb := hC F σ P n s p out hn2 hfan hdet
  by_contra! hs
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ A + 5 * η)
  change (A + 5 * η) * p.innerGates.card ≤
    (A + 5 * η) * ((K - ε) * (n : ℝ)^2) at hm
  dsimp only [δ] at hconst
  nlinarith

/-- The checked Gaussian layout coefficient gives `1.8906244… n²` determinant gates,
up to an arbitrarily small loss in the leading coefficient. -/
theorem lowerBound_determinant_gaussian {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (F : Type u) [Field F] (σ : Signature.{v})
      (P : (o : σ.Op) → MvPolynomial (Fin (σ.Arity o)) F)
      (s : ℕ) (p : Program σ (n * n) s) (out : Unit → Wire (n * n) s),
      p.FanInAtMost 2 → wirePolynomial P p (out ()) = determinant F n →
      (1 + 1 / (8 * Gaussian.gaussianCoefficient) - ε) * (n : ℝ)^2 <
        p.innerGates.card := by
  simpa only [← mul_assoc, show (4 : ℝ) * 2 = 8 by norm_num] using
    lowerBound_determinant.{u, v} (by positivity [Gaussian.gaussianCoefficient_pos])
      layoutBound_gaussian hε

end Frontier.Arithmetic
