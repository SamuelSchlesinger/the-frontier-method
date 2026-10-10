/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.AverageCase.Sweep
public import Frontier.Compiler

/-!
# Coherent frontier traces of unambiguous networks

Uniqueness of satisfying edge assignments makes the separator lemma splice the entire
frontier trace. This supplies the stronger interface needed by weighted peeling.
-/

@[expose] public section

namespace Frontier.Network

open Set

variable {U ι V E : Type*} (N : Network U ι V E) (π : Layout V) [Nonempty U]

/-- The sweep of a network with unique satisfying assignments preserves entire traces. -/
theorem sweep_coherent
    (hunique : ∀ x α β, N.Satisfies x α → N.Satisfies x β → α = β) :
    (N.sweep π).Coherent := by
  intro t x hx y hy hxy z hzx hzy
  change EqOn z x (N.revealedBy π t) at hzx
  change EqOn z y (N.revealedBy π t)ᶜ at hzy
  have hcut : EqOn (N.witness x) (N.witness y) (N.frontier π t) := by
    simpa only [sweep, frontierSweep, Prod.mk.injEq, true_and, frontierValues_eq_iff] using hxy
  by_cases ht : t ≤ Nat.card V
  · simp only [revealedBy, ht, ite_true] at hzx hzy
    obtain ⟨γ, hz, hnear, hfar⟩ :=
      (N.satisfies_witness hx).splice (N.satisfies_witness hy) hcut hzx hzy
    have hwz := hunique z (N.witness z) γ (N.satisfies_witness ⟨γ, hz⟩) hz
    constructor
    · intro u hu
      change ((), N.frontierValues π u (N.witness z)) = ((), N.frontierValues π u (N.witness x))
      refine Prod.ext rfl ?_
      apply (N.frontierValues_eq_iff π).2
      rw [hwz]
      intro e he
      apply hnear
      change (π (N.src e) : ℕ) < t ∨ (π (N.tgt e) : ℕ) < t
      change ¬((π (N.src e) : ℕ) < u ↔ (π (N.tgt e) : ℕ) < u) at he
      lia
    · intro u hu
      change ((), N.frontierValues π u (N.witness z)) = ((), N.frontierValues π u (N.witness y))
      refine Prod.ext rfl ?_
      apply (N.frontierValues_eq_iff π).2
      rw [hwz]
      intro e he
      by_cases hn : e ∈ N.touching (π.initial t)
      · apply (hnear hn).trans
        apply hcut
        change ¬((π (N.src e) : ℕ) < t ↔ (π (N.tgt e) : ℕ) < t)
        change (π (N.src e) : ℕ) < t ∨ (π (N.tgt e) : ℕ) < t at hn
        change ¬((π (N.src e) : ℕ) < u ↔ (π (N.tgt e) : ℕ) < u) at he
        lia
      · exact hfar hn
  · simp only [revealedBy, ht, ite_false] at hzx
    have hzx : z = x := funext fun i => hzx (mem_univ i)
    subst z
    refine ⟨fun _ _ => rfl, ?_⟩
    intro u hu
    have hu' : Nat.card V ≤ u := by lia
    change ((), N.frontierValues π u (N.witness x)) = ((), N.frontierValues π u (N.witness y))
    refine Prod.ext rfl ?_
    apply (N.frontierValues_eq_iff π).2
    rw [frontier, π.initial_of_card_le hu', Multigraph.cut_univ]
    exact eqOn_empty _ _

/-- Weighted peeling applied to the uniquely determined runs of a network. -/
theorem abs_sumOn_accepted_le [Finite ι] [Finite U] [Finite E]
    (hunique : ∀ x α β, N.Satisfies x α → N.Satisfies x β → α = β)
    {KL KR : ℕ} (hKL : 1 < KL) (hKR : 1 < KR)
    {weight cost : (ι → U) → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hweight : ∀ x, |weight x| ≤ a) (hc : ∀ x, 0 ≤ cost x)
    (hrect : RectangleBudget weight cost KL KR)
    {w d m : ℕ} (hw : ∀ t, (N.frontier π t).ncard ≤ w) (hd : N.MaxDegreeLE d)
    (hm : ∀ v, (N.readAt v).ncard ≤ m) :
    |sumOn weight N.accepted| ≤ sumOn cost N.accepted + a * ((KL - 1) * (KR - 1) *
      (Nat.card V * Nat.card U ^ (w + d + m) + Nat.card U ^ N.readᶜ.ncard) : ℕ) := by
  have H := (N.sweep π).abs_sumOn_le_of_budget (N.sweep_coherent π hunique)
    (Nat.succ_pos _) hKL hKR ha hweight hc hrect
  refine H.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ ha))
  exact_mod_cast Nat.mul_le_mul_left _ (N.transitionCount_sweep_le π hw hd hm)

end Frontier.Network
