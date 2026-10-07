/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Linear.Linearize
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Two independent infinitesimals and the formal Hessian

Evaluation in `F[ε][ε]` records the value, two directional derivatives, and the
mixed second derivative. No analytic differentiation, characteristic-zero
hypothesis, or division by a factorial is used.
-/

@[expose] public section

namespace Frontier.Arithmetic

open MvPolynomial TrivSqZeroExt
open scoped DualNumber

variable {F R : Type*} [CommRing F] [CommRing R] [Algebra F R] {n : ℕ}

/-- Taylor expansion over a dual-number algebra, with coefficients in any base ring. -/
theorem fst_aeval (f : MvPolynomial (Fin n) F) (x : Fin n → R[ε]) :
    (aeval x f).fst = aeval (fun i => (x i).fst) f :=
  comp_aeval_apply x (fstHom F R R) f

/-- The first-order coefficient of polynomial evaluation over an arbitrary algebra. -/
theorem snd_aeval (f : MvPolynomial (Fin n) F) (x : Fin n → R[ε]) :
    (aeval x f).snd = ∑ i, aeval (fun j => (x j).fst) (pderiv i f) * (x i).snd := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [aeval_C, pderiv_C, map_zero, zero_mul, Finset.sum_const_zero]
    rw [IsScalarTower.algebraMap_apply F R R[ε]]
    simp [algebraMap_eq_inl]
  | add f g hf hg => simp [hf, hg, add_mul, Finset.sum_add_distrib]
  | mul_X f i hf =>
    have hX (j : Fin n) :
        aeval (fun k => (x k).fst) (pderiv j (X i : MvPolynomial (Fin n) F)) =
          (Pi.single i 1 : Fin n → R) j := by
      by_cases h : j = i <;> simp [h, Ne.symm]
    rw [map_mul, aeval_X, DualNumber.snd_mul, fst_aeval, hf, Finset.sum_mul]
    simp only [pderiv_mul, map_add, map_mul, aeval_X, hX, add_mul,
      Finset.sum_add_distrib, Pi.single_apply, mul_ite, ite_mul, mul_one,
      mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [add_comm]
    exact congrArg (· + _) (Finset.sum_congr rfl fun j _ => mul_right_comm _ _ _)

variable (F) in
/-- Two independent square-zero directions. -/
abbrev Jet := F[ε][ε]

/-- Input `a + ε u + δ v`, with zero mixed coefficient. -/
def jet (a u v : F) : Jet F := inl (inl a + inr u) + inr (inl v)

@[simp] theorem jet_fst_fst (a u v : F) : (jet a u v).fst.fst = a := by simp [jet]
@[simp] theorem jet_fst_snd (a u v : F) : (jet a u v).fst.snd = u := by simp [jet]
@[simp] theorem jet_snd_fst (a u v : F) : (jet a u v).snd.fst = v := by simp [jet]
@[simp] theorem jet_snd_snd (a u v : F) : (jet a u v).snd.snd = 0 := by simp [jet]

/-- The directional derivative at `a`, as a linear functional of the direction. -/
noncomputable def differential (f : MvPolynomial (Fin n) F) (a : Fin n → F) :
    (Fin n → F) →ₗ[F] F :=
  ∑ i, eval a (pderiv i f) • LinearMap.proj i

theorem differential_apply (f : MvPolynomial (Fin n) F) (a u : Fin n → F) :
    differential f a u = ∑ i, eval a (pderiv i f) * u i := by
  simp [differential]

/-- The formal Hessian, valid in arbitrary characteristic. -/
noncomputable def hessian (f : MvPolynomial (Fin n) F) (a : Fin n → F) :
    Matrix (Fin n) (Fin n) F := fun i j => eval a (pderiv i (pderiv j f))

theorem jet_value (f : MvPolynomial (Fin n) F) (a u v : Fin n → F) :
    (aeval (fun i => jet (a i) (u i) (v i)) f).fst.fst = eval a f := by
  simp [fst_aeval, jet, aeval_eq_eval]

theorem jet_left (f : MvPolynomial (Fin n) F) (a u v : Fin n → F) :
    (aeval (fun i => jet (a i) (u i) (v i)) f).fst.snd = differential f a u := by
  simp [fst_aeval, snd_aeval, jet, differential_apply, aeval_eq_eval]

theorem jet_right (f : MvPolynomial (Fin n) F) (a u v : Fin n → F) :
    (aeval (fun i => jet (a i) (u i) (v i)) f).snd.fst = differential f a v := by
  simp [snd_aeval, fst_sum, fst_aeval, jet, differential_apply, aeval_eq_eval]

/-- The mixed coefficient is the Hessian paired with the two directions. -/
theorem jet_mixed (f : MvPolynomial (Fin n) F) (a u v : Fin n → F) :
    (aeval (fun i => jet (a i) (u i) (v i)) f).snd.snd =
      ∑ i, ∑ j, hessian f a i j * u i * v j := by
  simp only [snd_aeval, snd_sum, DualNumber.snd_mul, fst_aeval]
  simp only [jet, fst_add, fst_inl, fst_inr, add_zero, snd_add, snd_inl, snd_inr,
    zero_add, mul_zero, aeval_eq_eval, hessian, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Directions invisible to first order give exactly the unperturbed value. -/
theorem jet_eval_left (f : MvPolynomial (Fin n) F) (a u : Fin n → F)
    (hu : differential f a u = 0) :
    aeval (fun i => jet (a i) (u i) 0) f = jet (eval a f) 0 0 := by
  apply TrivSqZeroExt.ext <;> apply TrivSqZeroExt.ext
  · simpa only [jet_fst_fst, Pi.zero_apply] using jet_value f a u 0
  · simpa only [jet_fst_snd, Pi.zero_apply] using (jet_left f a u 0).trans hu
  · simpa using jet_right f a u 0
  · simpa using jet_mixed f a u 0

theorem jet_eval_right (f : MvPolynomial (Fin n) F) (a v : Fin n → F)
    (hv : differential f a v = 0) :
    aeval (fun i => jet (a i) 0 (v i)) f = jet (eval a f) 0 0 := by
  apply TrivSqZeroExt.ext <;> apply TrivSqZeroExt.ext
  · simpa only [jet_fst_fst, Pi.zero_apply] using jet_value f a 0 v
  · simpa using jet_left f a 0 v
  · simpa only [jet_snd_fst, Pi.zero_apply] using (jet_right f a 0 v).trans hv
  · simpa using jet_mixed f a 0 v

end Frontier.Arithmetic
