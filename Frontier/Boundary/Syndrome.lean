/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Boundary.Code
public import Mathlib.Algebra.Group.Indicator

/-!
# Sweeps with an additive consistency promise

Intersect a swept set with one fiber of an additive map. The original frontier
message together with the partial syndrome makes splicing preserve this promise.
For nested revealed sets, the old syndrome and the original complete transition
determine the new syndrome. Thus the transition count pays for one syndrome,
rather than two independently chosen syndromes.

For redundant parity inputs, the map tests `y - L x`. Its zero fiber is exactly
the set of consistent pairs. This construction retains the cost of checking that
promise; it does not claim that linearly many such checks are free.
-/

@[expose] public section

namespace Frontier.Sweep

open Set

variable {ι U M W : Type*} [AddCommGroup U] [AddCommGroup W]
  {S : Set (ι → U)} (P : Sweep S M) (R : (ι → U) →+ W)

/-- The contribution of the revealed inputs to a consistency check. -/
noncomputable def syndrome (t : ℕ) (x : ι → U) : W :=
  R ((P.revealed t).indicator x)

/-- Impose an additive promise by retaining one partial syndrome in the message. -/
noncomputable def restrictHom (a : W) : Sweep (S ∩ R ⁻¹' {a}) (M × W) where
  length := P.length
  revealed := P.revealed
  revealed_zero := P.revealed_zero
  revealed_length := P.revealed_length
  message t x := (P.message t x, P.syndrome R t x)
  message_length x hx y hy := by
    apply Prod.ext (P.message_length x hx.1 y hy.1)
    simpa only [syndrome, P.revealed_length, indicator_univ] using hx.2.trans hy.2.symm
  splice t x hx y hy hxy z hzx hzy := by
    refine ⟨P.splice t x hx.1 y hy.1 (congrArg Prod.fst hxy) z hzx hzy, ?_⟩
    have hz : z = (P.revealed t).indicator x + (P.revealed t)ᶜ.indicator y := by
      funext i
      by_cases hi : i ∈ P.revealed t
      · simp only [Pi.add_apply, indicator_of_mem hi,
          indicator_of_notMem (notMem_compl_iff.mpr hi), add_zero]
        exact hzx hi
      · simp only [Pi.add_apply, indicator_of_notMem hi,
          indicator_of_mem (mem_compl hi), zero_add]
        exact hzy hi
    have h : P.syndrome R t x = P.syndrome R t y := congrArg Prod.snd hxy
    change R z = a
    rw [hz, R.map_add, show R ((P.revealed t).indicator x) =
      R ((P.revealed t).indicator y) from h, ← R.map_add,
      indicator_self_add_compl]
    exact hy.2

/-- The old syndrome and new coordinates determine the syndrome update. -/
theorem syndrome_succ_eq {t : ℕ} (hmono : P.revealed t ⊆ P.revealed (t + 1))
    (x : ι → U) :
    P.syndrome R (t + 1) x = P.syndrome R t x + R ((P.newly t).indicator x) := by
  rw [syndrome, syndrome, ← R.map_add]
  congr 1
  funext i
  by_cases hi : i ∈ P.revealed t
  · simp [newly, indicator_of_mem (hmono hi), hi]
  · by_cases hi' : i ∈ P.revealed (t + 1)
    · simp [newly, hi, hi']
    · simp [newly, hi, hi']

/-- Equality of original transitions and old syndromes determines the complete
transition of the promise-enforcing sweep. -/
theorem restrictHom_transition_eq (a : W) {t : ℕ}
    (hmono : P.revealed t ⊆ P.revealed (t + 1)) {x y : ι → U}
    (htrans : P.transition t x = P.transition t y)
    (hsyn : P.syndrome R t x = P.syndrome R t y) :
    (P.restrictHom R a).transition t x = (P.restrictHom R a).transition t y := by
  have hnew : (P.newly t).indicator x = (P.newly t).indicator y := by
    apply indicator_congr
    intro i hi
    exact congrFun (congrArg (fun z => z.2.2) htrans) ⟨i, hi⟩
  have hnext : P.syndrome R (t + 1) x = P.syndrome R (t + 1) y := by
    rw [P.syndrome_succ_eq R hmono, P.syndrome_succ_eq R hmono, hsyn, hnew]
  have h := htrans
  simp only [transition, Prod.mk.injEq] at h
  exact Prod.ext (Prod.ext h.1 hsyn) (Prod.ext (Prod.ext h.2.1 hnext) h.2.2)

/-- Enforcing an additive promise costs at most one factor of the number of
syndromes. A layout must control this cost jointly with its original transitions. -/
theorem transitionCount_restrictHom_le [Finite ι] [Finite U] (a : W)
    (hmono : ∀ t < P.length, P.revealed t ⊆ P.revealed (t + 1)) :
    (P.restrictHom R a).transitionCount ≤ (range R).ncard * P.transitionCount := by
  have h := (P.restrictHom R a).transitionCount_le_codes
    (fun t x => (P.transition t x, P.syndrome R t x))
    (fun t => (P.transition t '' S) ×ˢ range R)
    (fun t _ => (toFinite _).prod (finite_range R))
    (fun t _ x hx => ⟨⟨x, hx.1, rfl⟩, ⟨_, rfl⟩⟩)
    (fun t ht x _ y _ hxy => P.restrictHom_transition_eq R a (hmono t ht)
      (congrArg Prod.fst hxy) (congrArg Prod.snd hxy))
  simpa only [restrictHom, ncard_prod, transitionCount, Finset.mul_sum, mul_comm] using h

end Frontier.Sweep

namespace Frontier.Sweep

open Set

variable {ι F M W : Type*} [Finite ι] [Field F] [Finite F]
  [AddCommGroup W] [Module F W] {S : Set (ι → F)}

/-- The one-syndrome cost for a linear promise is the field size raised to its
rank. This keeps redundant consistency equations from being counted twice. -/
theorem transitionCount_restrictLinear_le (P : Sweep S M) (R : (ι → F) →ₗ[F] W) (a : W)
    (hmono : ∀ t < P.length, P.revealed t ⊆ P.revealed (t + 1)) :
    (P.restrictHom R.toAddMonoidHom a).transitionCount ≤
      Nat.card F ^ Module.finrank F (LinearMap.range R) * P.transitionCount := by
  let _ := Fintype.ofFinite ι
  have hcard : (range R.toAddMonoidHom).ncard =
      Nat.card F ^ Module.finrank F (LinearMap.range R) := by
    rw [show range R.toAddMonoidHom = (↑(LinearMap.range R) : Set W) from rfl,
      ← Nat.card_coe_set_eq]
    change Nat.card ↥(LinearMap.range R) = _
    exact Module.natCard_eq_pow_finrank (K := F)
  simpa only [hcard] using P.transitionCount_restrictHom_le R.toAddMonoidHom a hmono

end Frontier.Sweep
