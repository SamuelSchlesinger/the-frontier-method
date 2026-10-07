/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Arithmetic.Hessian
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # The determinant polynomial and its Hessian at permutation matrices -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Frontier.Arithmetic

open MvPolynomial Matrix TrivSqZeroExt
open scoped Matrix DualNumber

variable {F R : Type*} [Field F] [CommRing R] {n : ℕ}

/-- The determinant in its `n²` distinct input variables. -/
noncomputable def determinant (F : Type*) [CommRing F] (n : ℕ) :
    MvPolynomial (Fin (n * n)) F :=
  Matrix.det (fun i j : Fin n => X (finProdFinEquiv (i, j)))

theorem aeval_determinant [Algebra F R] (x : Fin (n * n) → R) :
    aeval x (determinant F n) = Matrix.det (fun i j => x (finProdFinEquiv (i, j))) := by
  rw [determinant, AlgHom.map_det]
  congr 1
  ext i j
  simp

/-- A two-entry determinant update reduces to a `2 × 2` determinant. -/
theorem det_two_entries (i j k l : Fin n) (x y : R) :
    (1 + Matrix.single i j x + Matrix.single k l y).det =
      (1 + if j = i then x else 0) * (1 + if l = k then y else 0) -
        (if j = k then y else 0) * (if l = i then x else 0) := by
  let U : Matrix (Fin n) (Fin 2) R := fun r => ![if r = i then x else 0, if r = k then y else 0]
  let V : Matrix (Fin 2) (Fin n) R := ![fun c => if c = j then 1 else 0,
    fun c => if c = l then 1 else 0]
  have hUV : U * V = Matrix.single i j x + Matrix.single k l y := by
    ext r c
    simp only [U, V, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply,
      Matrix.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one, mul_ite, mul_one, mul_zero]
    split_ifs <;> grind
  rw [add_assoc, ← hUV, det_one_add_mul_comm, det_fin_two]
  simp [U, V, Matrix.mul_apply, mul_ite, ite_mul, eq_comm]

/-- The off-diagonal mixed coefficient at the identity is a signed matching. -/
theorem det_two_entries_mixed (i j k l : Fin n) (hij : i ≠ j) :
    ((1 + Matrix.single i j (jet (0 : F) 1 0) +
      Matrix.single k l (jet (0 : F) 0 1)).det).snd.snd =
      if i = l ∧ j = k then -1 else 0 := by
  rw [det_two_entries]
  simp only [ite_eq_right (Ne.symm hij), add_zero, one_mul]
  split_ifs <;> simp <;> grind

/-- Evaluate at a permutation matrix; columns are permuted from the identity. -/
noncomputable def permutationPoint (π : Equiv.Perm (Fin n)) : Fin (n * n) → F :=
  fun c => (1 : Matrix (Fin n) (Fin n) F) (finProdFinEquiv.symm c).1
    (π.symm (finProdFinEquiv.symm c).2)

theorem hessian_determinant_permutation (π : Equiv.Perm (Fin n))
    (i j k l : Fin n) (hij : i ≠ j) :
    hessian (determinant F n) (permutationPoint π)
      (finProdFinEquiv (i, π j)) (finProdFinEquiv (k, π l)) =
      if i = l ∧ j = k then -(π.sign : F) else 0 := by
  classical
  let u : Fin (n * n) → F := Pi.single (finProdFinEquiv (i, π j)) 1
  let v : Fin (n * n) → F := Pi.single (finProdFinEquiv (k, π l)) 1
  let Z : Matrix (Fin n) (Fin n) (Jet F) :=
    1 + Matrix.single i j (jet 0 1 0) + Matrix.single k l (jet 0 0 1)
  have hZ : (fun r c : Fin n => jet (permutationPoint π (finProdFinEquiv (r, c)))
      (u (finProdFinEquiv (r, c))) (v (finProdFinEquiv (r, c)))) =
      Z.submatrix id π.symm := by
    funext r c
    simp only [u, v, permutationPoint, Matrix.submatrix_apply,
      id_eq, Z, Matrix.add_apply, Matrix.single_apply, Pi.single_apply,
      finProdFinEquiv.injective.eq_iff,
      Prod.mk.injEq]
    ext <;> simp only [Matrix.one_apply, fst_add, snd_add, fst_one,
      snd_one, fst_zero, snd_zero, jet_fst_fst, jet_fst_snd, jet_snd_fst, jet_snd_snd,
      apply_ite (fun z : Jet F => z.fst), apply_ite (fun z : Jet F => z.snd),
      apply_ite (fun z : F[ε] => z.fst), apply_ite (fun z : F[ε] => z.snd),
      Equiv.symm_apply_apply, Equiv.eq_symm_apply, zero_add, add_zero,
      ite_self]
    all_goals (congr 1; simp only [eq_comm])
  have H := jet_mixed (determinant F n) (permutationPoint π) u v
  have HE := congrArg (fun z : Jet F => z.snd.snd)
    (aeval_determinant (F := F) (fun c => jet (permutationPoint π c) (u c) (v c)))
  rw [hZ, Matrix.det_permute'] at HE
  have hcoeff : ((Equiv.Perm.sign π.symm : Jet F) * Z.det).snd.snd =
      (π.sign : F) * Z.det.snd.snd := by
    simp
  rw [hcoeff, det_two_entries_mixed i j k l hij] at HE
  have HH := H.symm.trans HE
  simpa [u, v, Pi.single_apply, mul_ite, ite_mul] using HH

/-- The permutation sign stays nonzero over every field, including characteristic two. -/
theorem sign_cast_ne_zero (π : Equiv.Perm (Fin n)) : (π.sign : F) ≠ 0 := by
  rcases Int.units_eq_one_or π.sign with h | h <;> simp [h]

/-- Every determinant entry is a formal variable. Two distinct rows suffice to witness it. -/
theorem mem_vars_determinant (hn : 2 ≤ n) (c : Fin (n * n)) :
    c ∈ (determinant F n).vars := by
  classical
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨i, hi⟩ := exists_ne (finProdFinEquiv.symm c).1
  let π := Equiv.swap i (finProdFinEquiv.symm c).2
  have h := hessian_determinant_permutation (F := F) π i
    (finProdFinEquiv.symm c).1 (finProdFinEquiv.symm c).1 i hi
  have hc : finProdFinEquiv ((finProdFinEquiv.symm c).1, π i) = c := by
    rw [show π i = (finProdFinEquiv.symm c).2 from Equiv.swap_apply_left _ _]
    exact finProdFinEquiv.apply_symm_apply c
  rw [hc] at h
  by_contra hc
  have hd := pderiv_eq_zero_of_notMem_vars hc
  have hz : (π.sign : F) = 0 := by simpa [hessian, hd] using h.symm
  exact sign_cast_ne_zero π hz

end Frontier.Arithmetic
