/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.Compression
public import Frontier.Boundary.Forest

/-!
# One-source blocks form a forest

The quotient of an acyclic directed network need not be acyclic. Its blocks with
only one source (an incoming edge or an original source vertex), however, induce
a forest. The rank of a block is the least topological rank of one of its vertices.
Every edge entering a one-source block strictly increases that block rank, and
there is at most one such edge. This supplies the forest hypothesis of the
boundary capacity certificate; it does not supply an improved layout.
-/

@[expose] public section

namespace Frontier

/-- A graph with a rank and at most one lower-ranked neighbour at each vertex is a forest. -/
theorem isAcyclic_of_unique_lower {V : Type*} (G : SimpleGraph V) (rank : V → ℕ)
    (hne : ∀ v w, G.Adj v w → rank v ≠ rank w)
    (hunique : ∀ v a b, G.Adj v a → G.Adj v b →
      rank a < rank v → rank b < rank v → a = b) : G.IsAcyclic := by
  classical
  intro v p hp
  obtain ⟨w, hw, hmax⟩ := p.support.toFinset.exists_max_image rank
    ⟨v, List.mem_toFinset.mpr p.start_mem_support⟩
  have hw : w ∈ p.support := List.mem_toFinset.mp hw
  let q := p.rotate w hw
  have hq : q.IsCycle := hp.rotate hw
  have hleft := q.adj_snd hq.not_nil
  have hright := (q.adj_penultimate hq.not_nil).symm
  have hbound : ∀ a ∈ q.support, rank a ≤ rank w := by
    intro a ha
    exact hmax a (List.mem_toFinset.mpr ((p.mem_support_rotate_iff w hw).mp ha))
  exact hq.snd_ne_penultimate (hunique w q.snd q.penultimate hleft hright
    (lt_of_le_of_ne (hbound _ (q.getVert_mem_support 1)) (hne _ _ hleft.symm))
    (lt_of_le_of_ne (hbound _ (q.getVert_mem_support (q.length - 1)))
      (hne _ _ hright.symm)))

namespace Multigraph.Compression

open Finset

variable {V E : Type*} {G : Multigraph V E} {d : ℕ} (c : Compression G d)

/-- A vertex of least topological rank in a block. -/
theorem exists_first (rank : V → ℕ) (B : c.blocks) :
    ∃ v, c.blockOf v = B ∧ ∀ w, c.blockOf w = B → rank v ≤ rank w := by
  classical
  have hB : B.val.toFinset.Nonempty := by
    have h := c.ne_nil B.val B.property
    cases hb : B.val with
    | nil => exact False.elim (h hb)
    | cons v vs => exact ⟨v, by simp⟩
  obtain ⟨v, hv, hmin⟩ := B.val.toFinset.exists_min_image rank hB
  exact ⟨v, c.mem_iff_blockOf_eq.mp (List.mem_toFinset.mp hv),
    fun w hw => hmin w (List.mem_toFinset.mpr (c.mem_iff_blockOf_eq.mpr hw))⟩

variable [Finite E]

/-- Edges entering a block from another block. -/
noncomputable def incoming (B : c.blocks) : Finset E := by
  classical
  let _ := Fintype.ofFinite E
  exact univ.filter fun e => c.blockOf (G.src e) ≠ B ∧ c.blockOf (G.tgt e) = B

@[simp] theorem mem_incoming (B : c.blocks) (e : E) :
    e ∈ c.incoming B ↔ c.blockOf (G.src e) ≠ B ∧ c.blockOf (G.tgt e) = B := by
  classical
  simp [incoming]

/-- In a directed acyclic network, the incoming values determine the block's
outgoing values whenever each local operation is deterministic. Original inputs
are supplied through the local hypothesis. -/
theorem eqOn_block {A : Type*} (rank : V → ℕ)
    (horder : ∀ e, rank (G.src e) < rank (G.tgt e)) (B : c.blocks)
    (α β : E → A)
    (hlocal : ∀ v, c.blockOf v = B →
      (∀ e, G.tgt e = v → α e = β e) → ∀ e, G.src e = v → α e = β e)
    (hin : ∀ e ∈ c.incoming B, α e = β e) :
    ∀ e, c.blockOf (G.src e) = B → α e = β e := by
  have h : ∀ k, ∀ v, rank v = k → c.blockOf v = B →
      ∀ e, G.src e = v → α e = β e := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro v hv hB
      apply hlocal v hB
      intro e he
      by_cases hs : c.blockOf (G.src e) = B
      · exact ih _ (by simpa [he, hv] using horder e) _ rfl hs e rfl
      · exact hin e ((c.mem_incoming B e).mpr ⟨hs, he ▸ hB⟩)
  exact fun e he => h _ _ rfl he e rfl

/-- Incoming edges and original source vertices are counted together. -/
noncomputable def sourceLoad (sources : Finset V) (B : c.blocks) : ℕ := by
  classical
  exact (c.incoming B).card + (sources.filter fun v => c.blockOf v = B).card

/-- Every external edge enters exactly one block, and every original source lies
in exactly one block. -/
theorem sum_sourceLoad (sources : Finset V) :
    ∑ B, c.sourceLoad sources B = Nat.card c.External + sources.card := by
  classical
  let _ := Fintype.ofFinite E
  have hin : ∀ B, c.incoming B =
      (univ.filter fun e => e ∈ c.External).filter fun e => c.blockOf (G.tgt e) = B := by
    intro B
    ext e
    simp only [mem_incoming, mem_filter, External, Set.mem_ofPred_eq]
    grind
  simp only [sourceLoad, sum_add_distrib, hin]
  rw [sum_card_fiberwise_eq_card_filter, sum_card_fiberwise_eq_card_filter]
  simp only [mem_univ, filter_true]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- An acyclic network has a source in every block: either an original source or
an edge entering the block. -/
theorem sourceLoad_pos (rank : V → ℕ) (horder : ∀ e, rank (G.src e) < rank (G.tgt e))
    (sources : Finset V) (hsource : ∀ v, v ∈ sources ∨ ∃ e, G.tgt e = v)
    (B : c.blocks) : 0 < c.sourceLoad sources B := by
  classical
  obtain ⟨v, hv, hmin⟩ := c.exists_first rank B
  rcases hsource v with hs | ⟨e, he⟩
  · have hpos := card_pos.mpr (show (sources.filter fun w => c.blockOf w = B).Nonempty
        from ⟨v, mem_filter.mpr ⟨hs, hv⟩⟩)
    unfold sourceLoad
    lia
  · have hsrc : c.blockOf (G.src e) ≠ B := by
      intro h
      have := hmin (G.src e) h
      have := horder e
      rw [he] at this
      lia
    have hpos := card_pos.mpr (show (c.incoming B).Nonempty
        from ⟨e, (c.mem_incoming B e).mpr ⟨hsrc, he ▸ hv⟩⟩)
    unfold sourceLoad
    lia

/-- The marked quotient is acyclic even when the full directed quotient has cycles. -/
theorem oneSource_acyclic (rank : V → ℕ) (horder : ∀ e, rank (G.src e) < rank (G.tgt e))
    (sources : Finset V) (hsource : ∀ v, v ∈ sources ∨ ∃ e, G.tgt e = v) :
    (c.quotient.induce {B | c.sourceLoad sources B = 1}).IsAcyclic := by
  classical
  choose root hroot hmin using c.exists_first rank
  let r : c.blocks → ℕ := fun B => rank (root B)
  have hinc : ∀ e, c.blockOf (G.src e) ≠ c.blockOf (G.tgt e) →
      c.sourceLoad sources (c.blockOf (G.tgt e)) = 1 →
      r (c.blockOf (G.src e)) < r (c.blockOf (G.tgt e)) := by
    intro e he hload
    let B := c.blockOf (G.tgt e)
    have hemem : e ∈ c.incoming B := (c.mem_incoming B e).mpr ⟨he, rfl⟩
    have hinpos := card_pos.mpr ⟨e, hemem⟩
    have hcard : (c.incoming B).card ≤ 1 := by
      change (c.incoming B).card + _ = 1 at hload
      lia
    have hnosource : root B ∉ sources := by
      intro hs
      have hpos := card_pos.mpr (show (sources.filter fun v => c.blockOf v = B).Nonempty
        from ⟨root B, mem_filter.mpr ⟨hs, hroot B⟩⟩)
      change (c.incoming B).card + _ = 1 at hload
      lia
    obtain ⟨e₀, he₀⟩ := (hsource (root B)).resolve_left hnosource
    have hsrc : c.blockOf (G.src e₀) ≠ B := by
      intro hs
      have := hmin B (G.src e₀) hs
      have := horder e₀
      rw [he₀] at this
      lia
    have heq : e = e₀ := card_le_one.mp hcard e hemem e₀
      ((c.mem_incoming B e₀).mpr ⟨hsrc, he₀ ▸ hroot B⟩)
    have hlt : rank (G.src e) < rank (root B) := by simpa [heq, he₀] using horder e₀
    exact (hmin (c.blockOf (G.src e)) (G.src e) rfl).trans_lt hlt
  have hto : ∀ a b : {B // c.sourceLoad sources B = 1},
      c.quotient.Adj a.val b.val → r a.val < r b.val →
      ∃ e, c.blockOf (G.src e) = a.val ∧ c.blockOf (G.tgt e) = b.val := by
    intro a b hab hr
    obtain ⟨hne, e, he⟩ := hab
    rcases Sym2.eq_iff.mp he with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact ⟨e, hs, ht⟩
    · have h := hinc e (by simpa [hs, ht] using hne.symm) (ht ▸ a.property)
      rw [hs, ht] at h
      lia
  apply isAcyclic_of_unique_lower _ (fun a => r a.val)
  · intro a b hab hr
    change c.quotient.Adj a.val b.val at hab
    obtain ⟨hne, e, he⟩ := hab
    rcases Sym2.eq_iff.mp he with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · have h := hinc e (by simpa [hs, ht] using hne) (ht ▸ b.property)
      rw [hs, ht] at h
      lia
    · have h := hinc e (by simpa [hs, ht] using hne.symm) (ht ▸ a.property)
      rw [hs, ht] at h
      lia
  · intro b a a' hba hba' hab ha'b
    change c.quotient.Adj b.val a.val at hba
    change c.quotient.Adj b.val a'.val at hba'
    obtain ⟨e, hs, ht⟩ := hto a b hba.symm hab
    obtain ⟨e', hs', ht'⟩ := hto a' b hba'.symm ha'b
    have hcard : (c.incoming b.val).card ≤ 1 := by
      have h := b.property
      change (c.incoming b.val).card + _ = 1 at h
      lia
    have heq : e = e' := card_le_one.mp hcard e
      ((c.mem_incoming b.val e).mpr ⟨hs ▸ hba.ne.symm, ht⟩) e'
      ((c.mem_incoming b.val e').mpr ⟨hs' ▸ hba'.ne.symm, ht'⟩)
    exact Subtype.ext (hs.symm.trans (heq ▸ hs'))

/-- The cubic core contains at least `h/2-r` one-source blocks. The integer form
avoids division and is exact even when this lower bound is negative. -/
theorem card_le_twice_oneSource_add_sources (c : Compression G)
    (hc : c.Final) (hG : G.Connected) (two : 2 ≤ c.blocks.card)
    (rank : V → ℕ) (horder : ∀ e, rank (G.src e) < rank (G.tgt e))
    (sources : Finset V) (hsource : ∀ v, v ∈ sources ∨ ∃ e, G.tgt e = v) :
    c.blocks.card ≤ 2 * ((univ.filter fun B => c.sourceLoad sources B = 1).card +
      sources.card) := by
  classical
  have hpoint : ∀ B, 2 ≤ c.sourceLoad sources B +
      if c.sourceLoad sources B = 1 then 1 else 0 := by
    intro B
    have := c.sourceLoad_pos rank horder sources hsource B
    split_ifs <;> lia
  have hsum := sum_le_sum (s := univ) (fun B _ => hpoint B)
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_coe, smul_eq_mul,
    sum_boole] at hsum
  rw [c.sum_sourceLoad] at hsum
  have hdeg := c.quotient.sum_degrees_eq_twice_card_edges
  simp only [(c.isRegularOfDegree hc hG two).degree_eq, sum_const, card_univ,
    Fintype.card_coe, smul_eq_mul] at hdeg
  have hE : c.quotient.edgeFinset.card = Nat.card c.External := by
    rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset, c.edgeSet_quotient,
      (c.injOn_ends hc).ncard_image, Nat.card_coe_set_eq]
    rfl
  rw [hE] at hdeg
  lia

end Multigraph.Compression

end Frontier
