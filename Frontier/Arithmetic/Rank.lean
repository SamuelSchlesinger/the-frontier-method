/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# Bilinear rank from a boundary with a split kernel

If a bilinear form vanishes on `ker L × ker R`, its rank is at most the sum of
the ranks of `L` and `R`. If `L x + R y = 0` forces `L x = 0`, their ranges are
disjoint, and this sum is at most the dimension of their common target.
-/

@[expose] public section

namespace Frontier.Arithmetic

open Module LinearMap

variable {F X Y W : Type*} [Field F]
  [AddCommGroup X] [Module F X] [FiniteDimensional F X]
  [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y]
  [AddCommGroup W] [Module F W] [FiniteDimensional F W]

/-- Vanishing on a product of subspaces bounds the rank by their total codimension. -/
theorem bilinear_rank_add_le (B : X →ₗ[F] Y →ₗ[F] F)
    (U : Submodule F X) (V : Submodule F Y)
    (h : ∀ x ∈ U, ∀ y ∈ V, B x y = 0) :
    finrank F (range B) + finrank F U + finrank F V ≤ finrank F X + finrank F Y := by
  have hsub : U ≤ V.dualAnnihilator.comap B := by
    intro x hx
    exact (Submodule.mem_dualAnnihilator _).mpr (h x hx)
  have hdim : finrank F (V.dualAnnihilator.comap B) ≤
      finrank F V.dualAnnihilator + finrank F (ker B) := by
    have H := B.lift_rank_comap_le V.dualAnnihilator
    simp only [← Submodule.finrank_eq_rank, Cardinal.lift_natCast] at H
    exact_mod_cast H
  have := Submodule.finrank_mono hsub
  have := B.finrank_range_add_finrank_ker
  have := Subspace.finrank_add_finrank_dualAnnihilator_eq V
  lia

/-- Two boundary maps with disjoint images pay for the whole mixed bilinear rank. -/
theorem bilinear_rank_le_boundary (B : X →ₗ[F] Y →ₗ[F] F)
    (L : X →ₗ[F] W) (R : Y →ₗ[F] W)
    (hsplit : ∀ x y, L x + R y = 0 → L x = 0)
    (hzero : ∀ x, L x = 0 → ∀ y, R y = 0 → B x y = 0) :
    finrank F (range B) ≤ finrank F W := by
  have hB := bilinear_rank_add_le B (ker L) (ker R) hzero
  have hL := L.finrank_range_add_finrank_ker
  have hR := R.finrank_range_add_finrank_ker
  have hd : Disjoint (range L) (range R) := by
    rw [Submodule.disjoint_def]
    rintro z ⟨x, rfl⟩ ⟨y, hy⟩
    exact hsplit x (-y) (by simp [hy])
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (range L) (range R)
  rw [hd.eq_bot, finrank_bot, add_zero] at hdim
  have := Submodule.finrank_le (range L ⊔ range R)
  lia

end Frontier.Arithmetic
