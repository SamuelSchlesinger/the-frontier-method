/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Arithmetic.Jet
public import Frontier.Arithmetic.Rank

/-!
# Mixed Hessian rank from splicing

A polynomial boundary that permits splicing over two independent square-zero
directions bounds the mixed Hessian rank. The compiler supplies this property in
`Frontier.Arithmetic.Compiler`. The proof is algebraic, in arbitrary characteristic.
-/

@[expose] public section

namespace Frontier.Arithmetic

open MvPolynomial Set Module LinearMap
open scoped Matrix

variable {F : Type*} [Field F] {n : ℕ} {M : Type*}

open Classical in
/-- Extend a vector on a set of coordinates by zero. -/
noncomputable def extend (S : Set (Fin n)) : (S → F) →ₗ[F] (Fin n → F) where
  toFun u i := if h : i ∈ S then u ⟨i, h⟩ else 0
  map_add' u v := by ext i; by_cases h : i ∈ S <;> simp [h]
  map_smul' c u := by ext i; by_cases h : i ∈ S <;> simp [h]

@[simp] theorem extend_mem {S : Set (Fin n)} (u : S → F) (i : S) :
    extend S u i = u i := by simp [extend, i.property]

@[simp] theorem extend_notMem {S : Set (Fin n)} (u : S → F) {i : Fin n} (hi : i ∉ S) :
    extend S u i = 0 := by simp [extend, hi]

/-- Splicing preserves the boundary values and the scalar output on its own side.
Only evaluation in the two-direction infinitesimal algebra is needed. -/
def Splices (f : MvPolynomial (Fin n) F) (q : M → MvPolynomial (Fin n) F)
    (S : Set (Fin n)) : Prop :=
  ∀ x y z : Fin n → Jet F, (∀ m, aeval x (q m) = aeval y (q m)) →
    EqOn z x S → EqOn z y Sᶜ →
    (∀ m, aeval z (q m) = aeval x (q m)) ∧
      (aeval z f = aeval x f ∨ aeval z f = aeval y f)

/-- The differential of the whole boundary. -/
noncomputable def boundaryDifferential (q : M → MvPolynomial (Fin n) F) (a : Fin n → F) :
    (Fin n → F) →ₗ[F] (M → F) := .pi fun m => differential (q m) a

/-- A cancellation between the two input sides forces both boundary differentials to vanish. -/
theorem Splices.split {f : MvPolynomial (Fin n) F} {q : M → MvPolynomial (Fin n) F}
    {S : Set (Fin n)} (h : Splices f q S) (a : Fin n → F) (u : S → F) (v : ↥(Sᶜ) → F)
    (huv : boundaryDifferential q a (extend S u) +
      boundaryDifferential q a (extend Sᶜ v) = 0) :
    boundaryDifferential q a (extend S u) = 0 := by
  classical
  have hd (m : M) : differential (q m) a (extend S u + extend Sᶜ v) = 0 := by
    simpa [boundaryDifferential] using congrFun huv m
  obtain ⟨hb, _⟩ := h
    (fun i => jet (a i) ((extend S u + extend Sᶜ v) i) 0)
    (fun i => jet (a i) 0 0) (fun i => jet (a i) (extend S u i) 0)
    (fun m => (jet_eval_left (q m) a _ (hd m)).trans
      (jet_eval_left (q m) a 0 (map_zero _)).symm)
    (by intro i hi; simp [hi]) (by intro i hi; simp [show i ∉ S from hi])
  ext m
  have hm := congrArg (fun z : Jet F => z.fst.snd) (hb m)
  rw [jet_left, jet_left, hd] at hm
  exact hm

/-- The mixed derivative vanishes on the two kernels of the boundary differential. -/
theorem Splices.mixed_zero {f : MvPolynomial (Fin n) F} {q : M → MvPolynomial (Fin n) F}
    {S : Set (Fin n)} (h : Splices f q S) (a : Fin n → F) (u : S → F) (v : ↥(Sᶜ) → F)
    (hu : boundaryDifferential q a (extend S u) = 0)
    (hv : boundaryDifferential q a (extend Sᶜ v) = 0) :
    ∑ i, ∑ j, hessian f a i j * extend S u i * extend Sᶜ v j = 0 := by
  have hdu (m : M) : differential (q m) a (extend S u) = 0 := congrFun hu m
  have hdv (m : M) : differential (q m) a (extend Sᶜ v) = 0 := congrFun hv m
  obtain ⟨_, hf⟩ := h (fun i => jet (a i) (extend S u i) 0)
    (fun i => jet (a i) 0 (extend Sᶜ v i))
    (fun i => jet (a i) (extend S u i) (extend Sᶜ v i))
    (fun m => (jet_eval_left (q m) a _ (hdu m)).trans
      (jet_eval_right (q m) a _ (hdv m)).symm)
    (by intro i hi; simp [hi]) (by intro i hi; simp [show i ∉ S from hi])
  rcases hf with hf | hf
  all_goals
    have hm := congrArg (fun z : Jet F => z.snd.snd) hf
    simpa only [jet_mixed, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero] using hm

open Classical in
theorem sum_mul_extend (S : Set (Fin n)) (g : Fin n → F) (u : S → F) :
    ∑ i, g i * extend S u i = ∑ i : S, g i * u i :=
  Finset.sum_congr_set S _ _ (by intro i hi; simp [extend, hi])
    (by intro i hi; simp [hi])

open Classical in
/-- The Hessian block with one coordinate on each side of the input partition. -/
noncomputable def mixedHessian (f : MvPolynomial (Fin n) F) (a : Fin n → F)
    (S : Set (Fin n)) : Matrix S ↥(Sᶜ) F :=
  (hessian f a).submatrix Subtype.val Subtype.val

open Classical in
/-- Mixed Hessian rank with its finite-index instances kept internal. -/
noncomputable def mixedRank (f : MvPolynomial (Fin n) F) (a : Fin n → F)
    (S : Set (Fin n)) : ℕ := (mixedHessian f a S).rank

theorem mixedRank_eq (f : MvPolynomial (Fin n) F) (a : Fin n → F)
    (S : Set (Fin n)) [Fintype ↥(Sᶜ)] : mixedRank f a S = (mixedHessian f a S).rank := by
  exact congrArg (fun inst : Fintype ↥(Sᶜ) =>
    @Matrix.rank S ↥(Sᶜ) F inst _ (mixedHessian f a S)) (Subsingleton.elim _ _)

open Classical in
theorem mixed_pairing (f : MvPolynomial (Fin n) F) (a : Fin n → F)
    (S : Set (Fin n)) (u : S → F) (v : ↥(Sᶜ) → F) :
    ∑ i, ∑ j, hessian f a i j * extend S u i * extend Sᶜ v j =
      (mixedHessian f a S *ᵥ v) ⬝ᵥ u := by
  calc
    _ = ∑ i, (∑ j, hessian f a i j * extend Sᶜ v j) * extend S u i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => mul_right_comm _ _ _
    _ = ∑ i : S, (∑ j, hessian f a i j * extend Sᶜ v j) * u i :=
      sum_mul_extend S _ u
    _ = _ := by
      simp only [sum_mul_extend, mixedHessian, Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
      congr 1
      funext i
      congr 1
      congr 1
      ext j
      simp

open Classical in
/-- **Mixed-Hessian boundary bound.** One scalar boundary coordinate pays for at most
one unit of mixed Hessian rank, including when information travels in both directions. -/
theorem Splices.rank_mixedHessian_le [Fintype M] {f : MvPolynomial (Fin n) F}
    {q : M → MvPolynomial (Fin n) F} {S : Set (Fin n)} (h : Splices f q S)
    (a : Fin n → F) : (mixedHessian f a S).rank ≤ Fintype.card M := by
  let L := (boundaryDifferential q a).comp (extend S)
  let R := (boundaryDifferential q a).comp (extend Sᶜ)
  let B := (dotProductEquiv F S).toLinearMap.comp (mixedHessian f a S).mulVecLin
  have hsplit : ∀ v u, R v + L u = 0 → R v = 0 := by
    intro v u huv
    have hL : L u = 0 := h.split a u v (by simpa [L, R, add_comm] using huv)
    simpa [hL] using huv
  have hzero : ∀ v, R v = 0 → ∀ u, L u = 0 → B v u = 0 := by
    intro v hv u hu
    change (mixedHessian f a S *ᵥ v) ⬝ᵥ u = 0
    rw [← mixed_pairing]
    exact h.mixed_zero a u v hu hv
  have hB := bilinear_rank_le_boundary B R L hsplit hzero
  dsimp only [B] at hB
  rw [LinearMap.range_comp, LinearEquiv.finrank_map_eq] at hB
  simpa only [
    Module.finrank_pi, Module.finrank_self, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one, Matrix.rank] using hB

end Frontier.Arithmetic
