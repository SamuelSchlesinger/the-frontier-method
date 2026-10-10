/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.Gaussian
import Mathlib.Data.Finset.Max

/-!
# Packing pairs with small star gaps

An edge of a cubic simple graph meets at most five edges, including itself.
Consequently any eligible edge set has a matching with at least one fifth as
many edges. Removing a bad vertex discards at most three eligible edges.

For any nonnegative vertex gap `g` and threshold `τ>0`, this supplies a matching
all of whose endpoints have gap at most `τ`, with
`3 |V| τ ≤ 10 |M| τ + 6 ∑v g(v)`.
In particular, a small total gap leaves linearly many disjoint candidate pairs.
No probability estimate for those optimized pairs is assumed or proved here.
-/

@[expose] public section

namespace Frontier.PairLayout

open Finset

/-- A maximum disjoint subfamily covers the eligible family by its conflict neighborhoods. -/
theorem exists_disjoint_subfamily {I A : Type*} [DecidableEq A]
    (S : Finset I) (support : I → Finset A)
    {B : ℕ} (hne : ∀ i ∈ S, (support i).Nonempty)
    (hload : ∀ i ∈ S, (S.filter fun j => ¬Disjoint (support i) (support j)).card ≤ B) :
    ∃ M : Finset I, M ⊆ S ∧ (M : Set I).Pairwise (fun i j => Disjoint (support i) (support j)) ∧
      S.card ≤ B * M.card := by
  classical
  let family := S.powerset.filter fun M : Finset I =>
    (M : Set I).Pairwise (fun i j => Disjoint (support i) (support j))
  have hempty : ∅ ∈ family := by simp [family]
  obtain ⟨M, hM, hmax⟩ := family.exists_max_image card ⟨_, hempty⟩
  obtain ⟨hsub, hpair⟩ := mem_filter.mp hM
  have hMS : M ⊆ S := mem_powerset.mp hsub
  have hcover (i : I) (hi : i ∈ S) : ∃ j ∈ M, ¬Disjoint (support i) (support j) := by
    by_contra! h
    have hiM : i ∉ M := by
      intro hiM
      obtain ⟨a, ha⟩ := hne i hi
      exact (disjoint_left.mp (h i hiM)) ha ha
    have hins : insert i M ∈ family := by
      refine mem_filter.mpr ⟨mem_powerset.mpr (insert_subset hi hMS), ?_⟩
      intro j hj k hk hjk
      rcases mem_insert.mp hj with hj | hj
      · subst j
        rcases mem_insert.mp hk with hk | hk
        · subst k
          exact False.elim (hjk rfl)
        · exact h k hk
      · rcases mem_insert.mp hk with hk | hk
        · subst k
          exact (h j hj).symm
        · exact hpair hj hk hjk
    have hc := hmax (insert i M) hins
    rw [card_insert_of_notMem hiM] at hc
    lia
  refine ⟨M, hMS, hpair, ?_⟩
  have hcover' : S ⊆ M.biUnion (fun i => S.filter fun j => ¬Disjoint (support i) (support j)) := by
    intro j hj
    obtain ⟨i, hi, hji⟩ := hcover j hj
    exact mem_biUnion.mpr ⟨i, hi, mem_filter.mpr ⟨hj, fun hd => hji hd.symm⟩⟩
  calc
    S.card ≤ (M.biUnion fun i => S.filter fun j => ¬Disjoint (support i) (support j)).card :=
      card_le_card hcover'
    _ ≤ ∑ i ∈ M, (S.filter fun j => ¬Disjoint (support i) (support j)).card := card_biUnion_le
    _ ≤ ∑ _i ∈ M, B := sum_le_sum fun i hi => hload i (hMS hi)
    _ = B * M.card := by simp [Nat.mul_comm]

variable {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Every eligible edge in a cubic graph conflicts with at most five eligible edges. -/
theorem card_edge_conflicts_le (regular : H.IsRegularOfDegree 3)
    (S : Finset (Sym2 V)) (hS : S ⊆ H.edgeFinset) {e : Sym2 V} (he : e ∈ S) :
    (S.filter fun f => ¬Disjoint e.toFinset f.toFinset).card ≤ 5 := by
  classical
  induction e using Sym2.ind with
  | _ u v =>
  have hev : s(u, v) ∈ H.incidenceFinset u ∩ H.incidenceFinset v := by
    have he' := SimpleGraph.mem_edgeFinset.mp (hS he)
    exact mem_inter.mpr ⟨SimpleGraph.mem_incidenceFinset.mpr ⟨he', by simp⟩,
      SimpleGraph.mem_incidenceFinset.mpr ⟨he', by simp⟩⟩
  have hsub : S.filter (fun f => ¬Disjoint s(u, v).toFinset f.toFinset) ⊆
      H.incidenceFinset u ∪ H.incidenceFinset v := by
    intro f hf
    obtain ⟨hfS, hdis⟩ := mem_filter.mp hf
    obtain ⟨w, hw, hwf⟩ := not_disjoint_iff.mp hdis
    have hw' : w = u ∨ w = v := by simpa [Sym2.toFinset_mk_eq] using hw
    have hfE := SimpleGraph.mem_edgeFinset.mp (hS hfS)
    rcases hw' with rfl | rfl
    · exact mem_union_left _ (SimpleGraph.mem_incidenceFinset.mpr
        ⟨hfE, Sym2.mem_toFinset.mp hwf⟩)
    · exact mem_union_right _ (SimpleGraph.mem_incidenceFinset.mpr
        ⟨hfE, Sym2.mem_toFinset.mp hwf⟩)
  have hcard := card_union_add_card_inter (H.incidenceFinset u) (H.incidenceFinset v)
  have hpos := card_pos.mpr ⟨_, hev⟩
  rw [Frontier.card_incidenceFinset_of_regular regular u,
    Frontier.card_incidenceFinset_of_regular regular v] at hcard
  have := card_le_card hsub
  lia

/-- Any eligible edge set has a matching containing at least a fifth of its edges. -/
theorem exists_matching_in (regular : H.IsRegularOfDegree 3) (S : Finset (Sym2 V))
    (hS : S ⊆ H.edgeFinset) :
    ∃ M : Finset (Sym2 V), M ⊆ S ∧
      (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset) ∧
        S.card ≤ 5 * M.card := by
  classical
  apply exists_disjoint_subfamily S (fun e : Sym2 V => e.toFinset)
  · intro e _
    induction e using Sym2.ind with
    | _ u v => simp [Sym2.toFinset_mk_eq]
  · exact fun e he => card_edge_conflicts_le H regular S hS he

/-- Avoiding bad vertices loses at most three eligible edges per removed vertex. -/
theorem exists_matching_avoiding (regular : H.IsRegularOfDegree 3) (bad : Finset V) :
    ∃ M : Finset (Sym2 V), M ⊆ H.edgeFinset ∧
      (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset) ∧
      (∀ e ∈ M, ∀ v ∈ e, v ∉ bad) ∧ H.edgeFinset.card ≤ 5 * M.card + 3 * bad.card := by
  classical
  let S := H.edgeFinset.filter fun e => ∀ v ∈ e, v ∉ bad
  obtain ⟨M, hMS, hpair, hsize⟩ := exists_matching_in H regular S (filter_subset _ _)
  have hcover : H.edgeFinset ⊆ S ∪ bad.biUnion (fun v => H.incidenceFinset v) := by
    intro e he
    by_cases h : ∀ v ∈ e, v ∉ bad
    · exact mem_union_left _ (mem_filter.mpr ⟨he, h⟩)
    · push Not at h
      obtain ⟨v, hve, hv⟩ := h
      exact mem_union_right _ (mem_biUnion.mpr ⟨v, hv,
        SimpleGraph.mem_incidenceFinset.mpr ⟨SimpleGraph.mem_edgeFinset.mp he, hve⟩⟩)
  have hi := Gaussian.card_incidence_biUnion_le
    (H := H) (fun v => (regular.degree_eq v).le) bad
  have hc := (card_le_card hcover).trans (card_union_le _ _)
  refine ⟨M, fun e he => (mem_filter.mp (hMS he)).1, hpair,
    fun e he => (mem_filter.mp (hMS he)).2, ?_⟩
  lia

/-- A small total nonnegative gap leaves many disjoint adjacent pairs whose two gaps
are both below the chosen threshold. The cardinality bound is stated without division. -/
theorem exists_matching_small_gap (regular : H.IsRegularOfDegree 3) (gap : V → ℝ)
    (hgap : ∀ v, 0 ≤ gap v) {τ : ℝ} (hτ : 0 < τ) :
    ∃ M : Finset (Sym2 V), M ⊆ H.edgeFinset ∧
      (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset) ∧
      (∀ e ∈ M, ∀ v ∈ e, gap v ≤ τ) ∧
        3 * (Fintype.card V : ℝ) * τ ≤ 10 * M.card * τ + 6 * ∑ v, gap v := by
  classical
  let bad := univ.filter fun v => τ < gap v
  obtain ⟨M, hM, hpair, hgood, hsize⟩ := exists_matching_avoiding H regular bad
  have hbad : (bad.card : ℝ) * τ ≤ ∑ v, gap v := by
    calc
      _ = ∑ _v ∈ bad, τ := by simp
      _ ≤ ∑ v ∈ bad, gap v := sum_le_sum fun v hv => (mem_filter.mp hv).2.le
      _ ≤ ∑ v, gap v := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun v _ _ => hgap v)
  have hsize' : (H.edgeFinset.card : ℝ) ≤ 5 * M.card + 3 * bad.card := by exact_mod_cast hsize
  have hE := Gaussian.card_edgeFinset_of_regular regular
  refine ⟨M, hM, hpair, fun e he v hv => ?_, ?_⟩
  · have h := hgood e he v hv
    simpa [bad] using h
  · have hmul := mul_le_mul_of_nonneg_right hsize' hτ.le
    rw [hE] at hmul
    nlinarith

end Frontier.PairLayout
