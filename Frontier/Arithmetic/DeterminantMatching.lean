/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! # Permutation matchings across a matrix-entry partition -/

@[expose] public section

namespace Frontier.Arithmetic.DeterminantMatching

open Finset Equiv

/-- An ordered pair of distinct indices. -/
abbrev Pair (α : Type*) := {p : α × α // p.1 ≠ p.2}

variable {α : Type*}

/-- Simultaneously permute both entries of a distinct pair. -/
def mapPair (σ : Perm α) : Pair α ≃ Pair α where
  toFun p := ⟨(σ p.1.1, σ p.1.2), σ.injective.ne p.2⟩
  invFun p := ⟨(σ.symm p.1.1, σ.symm p.1.2), σ.symm.injective.ne p.2⟩
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp

theorem mapPair_transitive (p q : Pair α) : ∃ σ : Perm α, mapPair σ p = q := by
  let f : Bool → α := fun b => if b then p.1.1 else p.1.2
  let g : Bool → α := fun b => if b then q.1.1 else q.1.2
  have hf : Function.Injective f := by
    intro a b h
    cases a <;> cases b <;> simp_all [f, p.2, Ne.symm p.2]
  have hg : Function.Injective g := by
    intro a b h
    cases a <;> cases b <;> simp_all [g, q.2, Ne.symm q.2]
  obtain ⟨σ, hσ⟩ := Perm.exists_extending_pair f g hf hg
  refine ⟨σ, ?_⟩
  apply Subtype.ext
  exact Prod.ext (hσ true) (hσ false)

variable [Fintype α] [DecidableEq α]

open Classical in
/-- Double counting a transitive permutation orbit, without division or probabilities. -/
theorem sum_pair_action (g : Pair α → ℕ) (p : Pair α) :
    Fintype.card (Pair α) * (∑ σ : Perm α, g (mapPair σ p)) =
      Fintype.card (Perm α) * ∑ q, g q := by
  have hsame (q : Pair α) : ∑ σ : Perm α, g (mapPair σ q) =
      ∑ σ : Perm α, g (mapPair σ p) := by
    obtain ⟨τ, rfl⟩ := mapPair_transitive p q
    simpa only [mapPair, Equiv.coe_fn_mk, Equiv.coe_mulRight, Perm.mul_apply] using
      Equiv.sum_comp (Equiv.mulRight τ) (fun σ => g (mapPair σ p))
  calc
    _ = ∑ q : Pair α, ∑ σ : Perm α, g (mapPair σ q) := by simp [hsame]
    _ = ∑ σ : Perm α, ∑ q : Pair α, g (mapPair σ q) := Finset.sum_comm
    _ = _ := by simp only [(mapPair _).sum_comp, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.cast_id]

open Classical in
/-- Some permutation attains at least the mean number of prescribed pairs. -/
theorem exists_large_matching (g : Pair α → Pair α → ℕ) :
    ∃ σ : Perm α, (∑ p, ∑ q, g p q) ≤
      Fintype.card (Pair α) * ∑ p, g p (mapPair σ p) := by
  let f (σ : Perm α) := ∑ p, g p (mapPair σ p)
  obtain ⟨σ, _, hσ⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  have hsum : Fintype.card (Pair α) * (∑ τ, f τ) =
      Fintype.card (Perm α) * (∑ p, ∑ q, g p q) := by
    simp only [f, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => by
      simpa only [Finset.mul_sum] using sum_pair_action (g p) p
  have hle : (∑ τ, f τ) ≤ Fintype.card (Perm α) * f σ := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun τ hτ => hσ τ hτ)
  refine ⟨σ, ?_⟩
  have hpos := Fintype.card_pos (α := Perm α)
  have := Nat.mul_le_mul_left (Fintype.card (Pair α)) hle
  dsimp [f] at *
  nlinarith

/-- Two entries on opposite sides, in distinct rows and columns. -/
abbrev Good (S : Finset (α × α)) :=
  {z : (α × α) × (α × α) // z.1 ∈ S ∧ z.2 ∉ S ∧ z.1.1 ≠ z.2.1 ∧ z.1.2 ≠ z.2.2}

open Classical in
/-- Removing pairs in a common row or column costs at most two cubes. -/
theorem good_card_bound (S : Finset (α × α)) :
    S.card * Sᶜ.card ≤ Fintype.card (Good S) + 2 * Fintype.card α ^ 3 := by
  let f : S × ↥(Sᶜ) → Good S ⊕ ((α × α) × α) ⊕ ((α × α) × α) := fun z =>
    if hr : z.1.1.1 = z.2.1.1 then Sum.inr (Sum.inl (z.1.1, z.2.1.2))
    else if hc : z.1.1.2 = z.2.1.2 then Sum.inr (Sum.inr (z.1.1, z.2.1.1))
    else Sum.inl ⟨(z.1.1, z.2.1), z.1.2, (Finset.mem_compl.mp z.2.2), hr, hc⟩
  have hf : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    split_ifs at hab <;>
      simp only [Sum.inr.injEq, Sum.inl.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl,
        Prod.mk.injEq, Subtype.mk.injEq] at hab
    all_goals first | contradiction | (apply Prod.ext <;> apply Subtype.ext <;>
      apply Prod.ext <;> grind)
  have h := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_sum, pow_succ,
    pow_zero, mul_one, one_mul, two_mul, add_assoc] using h

/-- Reorder two matrix entries into their row pair and reversed column pair. -/
def goodEquiv (S : Finset (α × α)) : Good S ≃
    {z : Pair α × Pair α // (z.1.1.1, z.2.1.2) ∈ S ∧ (z.1.1.2, z.2.1.1) ∉ S} where
  toFun z := ⟨(⟨(z.1.1.1, z.1.2.1), z.2.2.2.1⟩,
    ⟨(z.1.2.2, z.1.1.2), Ne.symm z.2.2.2.2⟩), z.2.1, z.2.2.1⟩
  invFun z := ⟨((z.1.1.1.1, z.1.2.1.2), (z.1.1.1.2, z.1.2.1.1)),
    z.2.1, z.2.2, z.1.1.2, Ne.symm z.1.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

open Classical in
theorem good_card_eq (S : Finset (α × α)) :
    Fintype.card (Good S) = ∑ p : Pair α, ∑ q : Pair α,
      if (p.1.1, q.1.2) ∈ S ∧ (p.1.2, q.1.1) ∉ S then 1 else 0 := by
  rw [Fintype.card_congr (goodEquiv S), Fintype.card_subtype]
  rw [← Fintype.sum_prod_type (fun z : Pair α × Pair α =>
    if (z.1.1.1, z.2.1.2) ∈ S ∧ (z.1.1.2, z.2.1.1) ∉ S then (1 : ℕ) else 0)]
  simp

open Classical in
/-- The number of split off-diagonal matching edges, counted from the `S` endpoint. -/
noncomputable def crossing (S : Finset (α × α)) (σ : Perm α) : ℕ :=
  ∑ p : Pair α, if (p.1.1, σ p.1.2) ∈ S ∧ (p.1.2, σ p.1.1) ∉ S then 1 else 0

open Classical in
/-- A permutation with many split matching edges exists for every entry partition. -/
theorem exists_crossing (S : Finset (α × α)) :
    ∃ σ : Perm α, S.card * Sᶜ.card ≤
      (Fintype.card α)^2 * crossing S σ + 2 * (Fintype.card α)^3 := by
  obtain ⟨σ, hσ⟩ := exists_large_matching (fun p q =>
    if (p.1.1, q.1.2) ∈ S ∧ (p.1.2, q.1.1) ∉ S then 1 else 0)
  have hpair : Fintype.card (Pair α) ≤ (Fintype.card α)^2 := by
    simpa only [pow_two, Fintype.card_prod] using
      Fintype.card_subtype_le (fun p : α × α => p.1 ≠ p.2)
  have h := good_card_bound S
  rw [good_card_eq] at h
  refine ⟨σ, ?_⟩
  change _ ≤ Fintype.card (Pair α) * crossing S σ at hσ
  exact h.trans (Nat.add_le_add_right (hσ.trans (Nat.mul_le_mul_right _ hpair)) _)

end Frontier.Arithmetic.DeterminantMatching
