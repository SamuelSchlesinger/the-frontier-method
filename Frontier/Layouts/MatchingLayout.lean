/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.PairGeometry

/-!
# Assembling disjoint pairs in a simple graph

A matching partitions the vertices into unpaired vertices and two endpoints
per selected edge. The auxiliary cost keeps selected edges intact and pays
endpoint-to-port disagreements on the remaining edges. It bounds the original
cut and decomposes exactly over these blocks.
-/

@[expose] public section

namespace Frontier.PairLayout

open Finset Gaussian

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The vertices covered by selected edges. -/
def matchedVertices (M : Finset (Sym2 V)) : Finset V := M.biUnion Sym2.toFinset

/-- Vertices outside every selected pair. -/
def singleVertices (M : Finset (Sym2 V)) : Finset V := univ \ matchedVertices M

variable (H : SimpleGraph V) [DecidableRel H.Adj]

omit [DecidableEq V] in
theorem adjacent_out {e : Sym2 V} (he : e ∈ H.edgeFinset) : H.Adj e.out.1 e.out.2 := by
  apply (SimpleGraph.mem_edgeSet H).mp
  rw [Sym2.mk_fst_out_snd_out]
  exact SimpleGraph.mem_edgeFinset.mp he

omit [Fintype V] in
private theorem toFinset_out (e : Sym2 V) : e.toFinset = {e.out.1, e.out.2} := by
  conv_lhs => rw [← Sym2.mk_fst_out_snd_out e]
  exact Sym2.toFinset_mk_eq

/-- No endpoint is counted twice when selected edges form a matching. -/
theorem sum_vertices_eq_matching_blocks {A : Type*} [AddCommMonoid A]
    (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (f : V → A) :
    ∑ v, f v = (∑ v ∈ singleVertices M, f v) +
      ∑ e ∈ M, (f e.out.1 + f e.out.2) := by
  rw [← sum_sdiff (subset_univ (matchedVertices M)), matchedVertices, sum_biUnion hdisj]
  congr 1
  apply sum_congr rfl
  intro e he
  rw [toFinset_out, sum_pair (adjacent_out H (hM he)).ne]

/-- A matching uses exactly two vertices per edge. -/
theorem card_singleVertices_add_two_mul (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset)) :
    (singleVertices M).card + 2 * M.card = Fintype.card V := by
  simpa [Nat.mul_comm] using (sum_vertices_eq_matching_blocks H M hM hdisj (fun _ => (1 : ℕ))).symm

/-- The endpoints of a matching, indexed once each. -/
noncomputable def pairEndpoint (M : Finset (Sym2 V)) (x : ↥M × Bool) : V :=
  if x.2 then x.1.val.out.2 else x.1.val.out.1

omit [Fintype V] in
theorem pairEndpoint_mem (M : Finset (Sym2 V)) (x : ↥M × Bool) :
    pairEndpoint M x ∈ x.1.val.toFinset := by
  rcases x with ⟨e, b⟩
  cases b
  · simpa [pairEndpoint] using Sym2.out_fst_mem e.val
  · simpa [pairEndpoint] using Sym2.out_snd_mem e.val

/-- Different endpoint slots of a matching always name different vertices. -/
theorem pairEndpoint_injective (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset)) :
    Function.Injective (pairEndpoint M) := by
  rintro ⟨e, b⟩ ⟨f, c⟩ h
  have hef : e = f := by
    apply Subtype.ext
    by_contra hne
    exact (disjoint_left.mp (hdisj e.property f.property hne))
      (pairEndpoint_mem M (e, b)) (h.symm ▸ pairEndpoint_mem M (f, c))
  subst f
  have hne := (adjacent_out H (hM e.property)).ne
  cases b <;> cases c <;> simp_all [pairEndpoint]

/-- At an endpoint of a selected edge, it is the only selected incident edge. -/
theorem mem_matching_iff_eq_of_incident (M : Finset (Sym2 V))
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    {e : Sym2 V} (he : e ∈ M) {v : V} (hv : v ∈ e) {f : Sym2 V}
    (hf : f ∈ H.incidenceFinset v) : f ∈ M ↔ f = e := by
  constructor
  · intro hfM
    by_contra hne
    exact (disjoint_left.mp (hdisj hfM he hne))
      (Sym2.mem_toFinset.mpr (SimpleGraph.mem_incidenceFinset.mp hf).2)
      (Sym2.mem_toFinset.mpr hv)
  · rintro rfl
    exact he

/-- Reverse the two incidence sums, retaining exactly the unselected edges. -/
theorem sum_outer_incidence {A : Type*} [AddCommMonoid A]
    (M : Finset (Sym2 V)) (f : V → Sym2 V → A) :
    (∑ v, ∑ e ∈ H.incidenceFinset v \ M, f v e) =
      ∑ e ∈ H.edgeFinset \ M, (f e.out.1 e + f e.out.2 e) := by
  have hi (v) : H.incidenceFinset v \ M =
      (H.edgeFinset \ M).filter (fun e => v ∈ e) := by
    ext e
    simp only [mem_sdiff, mem_filter, SimpleGraph.incidenceFinset_eq_filter]
    aesop
  simp_rw [hi, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  rw [← sum_filter]
  have hv : univ.filter (fun v => v ∈ e) = e.toFinset := by ext v; simp
  rw [hv, toFinset_out, sum_pair (adjacent_out H (mem_sdiff.mp he).1).ne]

/-- Endpoint-to-port disagreement on the external incidences at one vertex. -/
noncomputable def outerCost (M : Finset (Sym2 V)) (port : Sym2 V → Bool)
    (color : V → Bool) (v : V) : ℕ :=
  ∑ e ∈ H.incidenceFinset v \ M, portDisagreement (color v) (port e)

/-- At a selected endpoint, the other two incident edges are exactly its outer ports. -/
theorem outerCost_eq_two (M : Finset (Sym2 V)) (port : Sym2 V → Bool) (color : V → Bool)
    {v : V} (E : Fin 3 ≃ ↥(H.incidenceFinset v))
    (hmem : ∀ e ∈ H.incidenceFinset v, e ∈ M ↔ e = (E 0).val) :
    outerCost H M port color v = portDisagreement (color v) (port (E 1)) +
      portDisagreement (color v) (port (E 2)) := by
  have hi (i : Fin 3) : (E i).val ∈ M ↔ i = 0 := by
    rw [hmem _ (E i).property]
    exact ⟨fun h => E.injective (Subtype.ext h), fun h => by rw [h]⟩
  calc
    outerCost H M port color v = ∑ e : ↥(H.incidenceFinset v),
        if e.val ∉ M then portDisagreement (color v) (port e) else 0 := by
      rw [outerCost, sdiff_eq_filter, sum_filter]
      exact (sum_coe_sort (H.incidenceFinset v)
        (fun e => if e ∉ M then portDisagreement (color v) (port e) else 0)).symm
    _ = ∑ i : Fin 3, if (E i).val ∉ M then
        portDisagreement (color v) (port (E i)) else 0 := (E.sum_comp _).symm
    _ = _ := by simp [hi, Fin.sum_univ_succ]

/-- An unpaired vertex retains all three incident ports. -/
theorem outerCost_eq_three (M : Finset (Sym2 V)) (port : Sym2 V → Bool) (color : V → Bool)
    {v : V} (hv : v ∈ singleVertices M) (E : Fin 3 ≃ ↥(H.incidenceFinset v)) :
    outerCost H M port color v = portDisagreement (color v) (port (E 0)) +
      portDisagreement (color v) (port (E 1)) + portDisagreement (color v) (port (E 2)) := by
  have heq : H.incidenceFinset v \ M = H.incidenceFinset v := by
    ext e
    simp only [mem_sdiff]
    refine ⟨And.left, fun he => ⟨he, ?_⟩⟩
    intro heM
    exact (mem_sdiff.mp hv).2 (mem_biUnion.mpr ⟨e, heM,
      Sym2.mem_toFinset.mpr (SimpleGraph.mem_incidenceFinset.mp he).2⟩)
  rw [outerCost, heq, ← sum_coe_sort, ← E.sum_comp]
  simp [Fin.sum_univ_succ, add_assoc]

/-- The four external half-edges and the intact central edge are precisely the
five terms in the two-vertex energy. -/
theorem pair_block_cost (M : Finset (Sym2 V))
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    {u v : V} (p : CubicPair H u v) (he : s(u, v) ∈ M)
    (port : Sym2 V → Bool) (color : V → Bool) :
    portDisagreement (color u) (color v) + outerCost H M port color u +
      outerCost H M port color v =
        twoVertexEnergy (port (p.outerEdges 0)) (port (p.outerEdges 1))
          (port (p.outerEdges 2)) (port (p.outerEdges 3)) (color u) (color v) := by
  have hl := outerCost_eq_two H M port color (CubicPair.incidenceEnum p.leftNeighbors)
    (fun e he' => by
      simpa [CubicPair.incidenceEnum_apply, p.left_zero] using
        mem_matching_iff_eq_of_incident H M hdisj he (by simp : u ∈ s(u, v)) he')
  have hr := outerCost_eq_two H M port color (CubicPair.incidenceEnum p.rightNeighbors)
    (fun e he' => by
      simpa [CubicPair.incidenceEnum_apply, p.right_zero, Sym2.eq_swap] using
        mem_matching_iff_eq_of_incident H M hdisj he (by simp : v ∈ s(u, v)) he')
  rw [hl, hr]
  simp only [CubicPair.incidenceEnum_apply, CubicPair.outerEdges, CubicPair.vertices,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
    twoVertexEnergy]
  lia

/-- Intact selected edges together with all external half-edge costs. -/
noncomputable def matchingPortCost (M : Finset (Sym2 V)) (port : Sym2 V → Bool)
    (color : V → Bool) : ℕ :=
  (∑ e ∈ M, portDisagreement (color e.out.1) (color e.out.2)) +
    ∑ v, outerCost H M port color v

/-- The auxiliary cost partitions exactly over singleton and pair blocks. -/
theorem matchingPortCost_eq_blocks (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (port : Sym2 V → Bool) (color : V → Bool) :
    matchingPortCost H M port color =
      (∑ v ∈ singleVertices M, outerCost H M port color v) +
      ∑ e ∈ M, (portDisagreement (color e.out.1) (color e.out.2) +
        outerCost H M port color e.out.1 + outerCost H M port color e.out.2) := by
  rw [matchingPortCost, sum_vertices_eq_matching_blocks H M hM hdisj]
  simp only [sum_add_distrib]
  lia

omit [DecidableEq V] in
/-- Boolean crossings count the original graph cut, independently of edge orientation. -/
theorem sum_disagreement_eq_card_cut (color : V → Bool) :
    (∑ e ∈ H.edgeFinset, portDisagreement (color e.out.1) (color e.out.2)) =
      (H.cutFinset (univ.filter fun v => color v = true)).card := by
  have hd (a b : Bool) : portDisagreement a b = if a ≠ b then 1 else 0 := by
    cases a <;> cases b <;> decide
  simp_rw [hd, sum_boole]
  apply congrArg Finset.card
  ext e
  have ho := Sym2.mk_fst_out_snd_out e
  rw [← ho]
  simp only [mem_filter, SimpleGraph.mem_cutFinset_mk]
  have hAdj : s(e.out.1, e.out.2) ∈ H.edgeFinset ↔ H.Adj e.out.1 e.out.2 :=
    SimpleGraph.mem_edgeFinset
  rw [hAdj, ho]
  cases color e.out.1 <;> cases color e.out.2 <;> simp

/-- Every original crossing is paid for by the intact edge or its external half-edges. -/
theorem card_cut_le_matchingPortCost (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (port : Sym2 V → Bool) (color : V → Bool) :
    (H.cutFinset (univ.filter fun v => color v = true)).card ≤
      matchingPortCost H M port color := by
  rw [← sum_disagreement_eq_card_cut]
  have hs := sum_sdiff (f := fun e => portDisagreement (color e.out.1) (color e.out.2)) hM
  unfold matchingPortCost outerCost
  rw [sum_outer_incidence]
  rw [← hs, add_comm]
  apply Nat.add_le_add_left
  apply sum_le_sum
  intro e _
  cases color e.out.1 <;> cases color e.out.2 <;> cases port e <;> decide

/-- A median key pays the optimal cubic-star cost at every threshold. -/
theorem threePortCost_median (a b c t : ℝ) :
    portDisagreement (belowThreshold t (LocalLayout.median3 a b c)) (belowThreshold t a) +
      portDisagreement (belowThreshold t (LocalLayout.median3 a b c)) (belowThreshold t b) +
      portDisagreement (belowThreshold t (LocalLayout.median3 a b c)) (belowThreshold t c) =
        starCost (belowThreshold t a) (belowThreshold t b) (belowThreshold t c) := by
  by_cases ha : a < t <;> by_cases hb : b < t <;> by_cases hc : c < t <;>
    simp [belowThreshold, LocalLayout.median3, max_lt_iff, min_lt_iff,
      portDisagreement, starCost, ha, hb, hc]

/-- Sum the optimized singleton and pair costs over the actual vertex partition. -/
noncomputable def matchingCost (M : Finset (Sym2 V))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2) (port : Sym2 V → Bool) : ℕ :=
  (∑ v ∈ singleVertices M, starCost (port s(v, (stars v 0).val))
    (port s(v, (stars v 1).val)) (port s(v, (stars v 2).val))) +
  ∑ e : ↥M, twoVertexCost (port ((pairs e).outerEdges 0)) (port ((pairs e).outerEdges 1))
    (port ((pairs e).outerEdges 2)) (port ((pairs e).outerEdges 3))

/-- Use a median score at each singleton and the explicit optimized keys at
the endpoints of each pair. This is one real key, chosen before any threshold. -/
noncomputable def matchingKey (M : Finset (Sym2 V))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2) (score : Sym2 V → ℝ) : V → ℝ :=
  Function.extend (pairEndpoint M)
    (fun x : ↥M × Bool =>
      let a := fun i => score ((pairs x.1).outerEdges i)
      if x.2 then pairKey (a 2) (a 3) (a 0) (a 1) else pairKey (a 0) (a 1) (a 2) (a 3))
    (fun v => LocalLayout.median3 (score s(v, (stars v 0).val))
      (score s(v, (stars v 1).val)) (score s(v, (stars v 2).val)))

omit [DecidableRel H.Adj] in
theorem matchingKey_single (M : Finset (Sym2 V))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2) (score : Sym2 V → ℝ)
    {v : V} (hv : v ∈ singleVertices M) :
    matchingKey H M stars pairs score v = LocalLayout.median3 (score s(v, (stars v 0).val))
      (score s(v, (stars v 1).val)) (score s(v, (stars v 2).val)) := by
  unfold matchingKey
  apply Function.extend_apply'
  rintro ⟨x, hx⟩
  exact (mem_sdiff.mp hv).2 (mem_biUnion.mpr
    ⟨x.1.val, x.1.property, hx ▸ pairEndpoint_mem M x⟩)

theorem matchingKey_pair (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2) (score : Sym2 V → ℝ)
    (x : ↥M × Bool) :
    matchingKey H M stars pairs score (pairEndpoint M x) =
      (let a := fun i => score ((pairs x.1).outerEdges i)
       if x.2 then pairKey (a 2) (a 3) (a 0) (a 1) else pairKey (a 0) (a 1) (a 2) (a 3)) :=
  (pairEndpoint_injective H M hM hdisj).extend_apply _ _ x

/-- The explicit vertex keys simultaneously attain every singleton and pair
minimum at every threshold. -/
theorem matchingPortCost_matchingKey (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2) (score : Sym2 V → ℝ) :
    ∀ t, matchingPortCost H M (fun e => belowThreshold t (score e))
      (fun v => belowThreshold t (matchingKey H M stars pairs score v)) =
        matchingCost H M stars pairs (fun e => belowThreshold t (score e)) := by
  let single := fun v => LocalLayout.median3 (score s(v, (stars v 0).val))
    (score s(v, (stars v 1).val)) (score s(v, (stars v 2).val))
  let a := fun (e : ↥M) i => score ((pairs e).outerEdges i)
  let pair := fun x : ↥M × Bool => if x.2 then pairKey (a x.1 2) (a x.1 3) (a x.1 0) (a x.1 1)
    else pairKey (a x.1 0) (a x.1 1) (a x.1 2) (a x.1 3)
  let key := matchingKey H M stars pairs score
  have hsingle : ∀ v ∈ singleVertices M, key v = single v :=
    fun _ hv => matchingKey_single H M stars pairs score hv
  have hpair : ∀ x, key (pairEndpoint M x) = pair x :=
    matchingKey_pair H M hM hdisj stars pairs score
  intro t
  change matchingPortCost H M (fun e => belowThreshold t (score e))
    (fun v => belowThreshold t (key v)) = _
  rw [matchingPortCost_eq_blocks H M hM hdisj, matchingCost]
  congr 1
  · apply sum_congr rfl
    intro v hv
    rw [outerCost_eq_three H M _ _ hv (CubicPair.incidenceEnum (stars v)), hsingle v hv]
    simp only [CubicPair.incidenceEnum_apply]
    exact threePortCost_median _ _ _ _
  · rw [← sum_coe_sort M]
    apply sum_congr rfl
    intro e _
    rw [pair_block_cost H M hdisj (pairs e) (by
      rw [Sym2.mk_fst_out_snd_out]
      exact e.property) (fun e => belowThreshold t (score e))
        (fun v => belowThreshold t (key v))]
    have hl : key e.val.out.1 = pairKey (a e 0) (a e 1) (a e 2) (a e 3) :=
      hpair (e, false)
    have hr : key e.val.out.2 = pairKey (a e 2) (a e 3) (a e 0) (a e 1) :=
      hpair (e, true)
    rw [hl, hr]
    exact twoVertexEnergy_pairKey _ _ _ _ _

/-- Optimized costs of disjoint pairs and remaining singletons bound every real
threshold cut of one common vertex key. -/
theorem card_cut_matchingKey_le (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2) (score : Sym2 V → ℝ) :
    ∀ t, (H.cutFinset (univ.filter fun v => matchingKey H M stars pairs score v < t)).card ≤
      matchingCost H M stars pairs (fun e => belowThreshold t (score e)) := by
  intro t
  have h := card_cut_le_matchingPortCost H M hM (fun e => belowThreshold t (score e))
    (fun v => belowThreshold t (matchingKey H M stars pairs score v))
  rw [matchingPortCost_matchingKey H M hM hdisj stars pairs score t] at h
  simpa only [belowThreshold, ite_eq_left_iff, Bool.false_eq_true, imp_false, not_not] using h

private theorem median3_mem (a b c : ℝ) :
    LocalLayout.median3 a b c = a ∨ LocalLayout.median3 a b c = b ∨
      LocalLayout.median3 a b c = c := by
  unfold LocalLayout.median3
  rcases max_choice (min a b) (min (max a b) c) with h | h
  · rw [h]
    rcases min_choice a b with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rw [h]
    rcases min_choice (max a b) c with h | h
    · rw [h]
      rcases max_choice a b with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

omit [DecidableRel H.Adj] in
/-- Both centers are within one step of an endpoint of each outer edge. -/
theorem CubicPair.mem_outerSupport {u v : V} (p : CubicPair H u v) (i : Fin 4) :
    u ∈ edgeSupport H 1 (p.outerEdges i) ∧ v ∈ edgeSupport H 1 (p.outerEdges i) := by
  have hu : u ∈ ball H v 1 :=
    ball_subset_ball_of_adj H p.adjacent.symm 0 (mem_ball_self H u 0)
  have hv : v ∈ ball H u 1 :=
    ball_subset_ball_of_adj H p.adjacent 0 (mem_ball_self H v 0)
  fin_cases i <;> constructor <;> apply mem_union_left <;>
    first | exact mem_ball_self H _ 1 | exact hu | exact hv

/-- Every optimized key selects an actual edge score from within one step of its vertex. -/
theorem matchingKey_source (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2) (score : Sym2 V → ℝ) (v : V) :
    ∃ e ∈ H.edgeFinset, v ∈ edgeSupport H 1 e ∧
      matchingKey H M stars pairs score v = score e := by
  by_cases hv : v ∈ singleVertices M
  · rw [matchingKey_single H M stars pairs score hv]
    have hs (i : Fin 3) : s(v, (stars v i).val) ∈ H.edgeFinset ∧
        v ∈ edgeSupport H 1 s(v, (stars v i).val) :=
      ⟨SimpleGraph.mem_edgeFinset.mpr (stars v i).property,
        mem_union_left _ (mem_ball_self H v 1)⟩
    rcases median3_mem (score s(v, (stars v 0).val)) (score s(v, (stars v 1).val))
      (score s(v, (stars v 2).val)) with h | h | h
    · exact ⟨_, (hs 0).1, (hs 0).2, h⟩
    · exact ⟨_, (hs 1).1, (hs 1).2, h⟩
    · exact ⟨_, (hs 2).1, (hs 2).2, h⟩
  · have hv' : v ∈ matchedVertices M := by simpa [singleVertices] using hv
    obtain ⟨e, he, hv⟩ := mem_biUnion.mp hv'
    rw [toFinset_out, mem_insert, mem_singleton] at hv
    let e' : ↥M := ⟨e, he⟩
    have hp (b : Bool) : ∃ i : Fin 4,
        matchingKey H M stars pairs score (pairEndpoint M (e', b)) =
          score ((pairs e').outerEdges i) := by
      rw [matchingKey_pair H M hM hdisj stars pairs score (e', b)]
      let a := fun i => score ((pairs e').outerEdges i)
      cases b
      · rcases pairKey_mem (a 0) (a 1) (a 2) (a 3) with h | h | h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
        · exact ⟨2, h⟩
        · exact ⟨3, h⟩
      · rcases pairKey_mem (a 2) (a 3) (a 0) (a 1) with h | h | h | h
        · exact ⟨2, h⟩
        · exact ⟨3, h⟩
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
    rcases hv with rfl | rfl
    · obtain ⟨i, hi⟩ := hp false
      exact ⟨_, (pairs e').outerEdges_mem i, ((pairs e').mem_outerSupport H i).1, hi⟩
    · obtain ⟨i, hi⟩ := hp true
      exact ⟨_, (pairs e').outerEdges_mem i, ((pairs e').mem_outerSupport H i).2, hi⟩

/-- A degree bound controls how many vertex keys can select any one edge score. -/
theorem card_edgeSupport_one_le {d : ℕ} (hd : 2 ≤ d) (degree : ∀ v, H.degree v ≤ d)
    (e : Sym2 V) : (edgeSupport H 1 e).card ≤ 2 * d ^ 2 := by
  induction e using Sym2.ind with
  | _ u v =>
    calc
      _ ≤ (ball H u 1).card + (ball H v 1).card := card_union_le _ _
      _ ≤ d ^ 2 + d ^ 2 := add_le_add
        (card_ball_le_degree H hd degree u 1) (card_ball_le_degree H hd degree v 1)
      _ = 2 * d ^ 2 := by lia

/-- Ties between optimized vertex keys have bounded multiplicity relative to edge-score ties. -/
theorem card_matchingKey_ties_le (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2) (score : Sym2 V → ℝ)
    {d T : ℕ} (hd : 2 ≤ d) (degree : ∀ v, H.degree v ≤ d)
    (htie : ∀ a, (H.edgeFinset.filter fun e => score e = a).card ≤ T) (a : ℝ) :
    (univ.filter fun v => matchingKey H M stars pairs score v = a).card ≤ T * (2 * d ^ 2) := by
  classical
  let scope := fun v => univ.filter (fun e : ↥H.edgeFinset => v ∈ edgeSupport H 1 e)
  apply card_ties_le_of_sources (fun e : ↥H.edgeFinset => score e)
    (matchingKey H M stars pairs score) scope
  · intro v
    obtain ⟨e, he, hv, hk⟩ := matchingKey_source H M hM hdisj stars pairs score v
    exact ⟨⟨e, he⟩, mem_filter.mpr ⟨mem_univ _, hv⟩, hk⟩
  · intro e
    calc
      _ ≤ (edgeSupport H 1 e).card := card_le_card fun v hv => by simpa [scope] using hv
      _ ≤ 2 * d ^ 2 := card_edgeSupport_one_le H hd degree e
  · intro a
    have hc : (univ.filter fun e : ↥H.edgeFinset => score e = a).card =
        (H.edgeFinset.filter fun e => score e = a).card := by
      apply card_bij (fun e _ => e.val)
      · intro e he
        exact mem_filter.mpr ⟨e.property, (mem_filter.mp he).2⟩
      · intro e he f hf hef
        exact Subtype.ext hef
      · intro e he
        exact ⟨⟨e, (mem_filter.mp he).1⟩,
          mem_filter.mpr ⟨mem_univ _, (mem_filter.mp he).2⟩, rfl⟩
    exact hc.le.trans (htie a)

omit [DecidableEq V] in
/-- Real-threshold cut bounds and tie bounds give an injective ordering of a simple graph. -/
theorem exists_key_of_threshold_bounds (score : V → ℝ) {d B T : ℕ}
    (degree : ∀ v, H.degree v ≤ d)
    (hbound : ∀ t, (H.cutFinset (univ.filter fun v => score v < t)).card ≤ B)
    (htie : ∀ a, (univ.filter fun v => score v = a).card ≤ T) :
    ∃ key : V → ℕ, Function.Injective key ∧
      ∀ t, (H.cutFinset (univ.filter fun v => key v < t)).card ≤ B + d * T := by
  classical
  let G : Hypergraph V (Sym2 V) := fun e => {v | e ∈ H.edgeFinset ∧ v ∈ e}
  have hcut (P : V → Prop) [DecidablePred P] :
      (G.cut {v | P v}).ncard = (H.cutFinset (univ.filter P)).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      simp only [Hypergraph.cut, G, Set.mem_ofPred_eq, Set.nonempty_def,
        Set.mem_inter_iff, Set.mem_sdiff, Finset.mem_coe,
        SimpleGraph.mem_edgeFinset, Sym2.mem_iff, SimpleGraph.mem_cutFinset_mk,
        mem_filter, mem_univ, true_and]
      aesop
  obtain ⟨key, hinj, hkey⟩ := G.exists_key_cut_le score (d := d) (B := B) (M := T)
    (fun v => by
      have hi : {e | v ∈ G e} = (↑(H.incidenceFinset v) : Set (Sym2 V)) := by
        ext e
        simp [G, SimpleGraph.incidenceSet]
      rw [hi, Set.ncard_coe_finset, SimpleGraph.card_incidenceFinset_eq_degree]
      exact degree v)
    (fun t => (hcut _).le.trans (hbound t)) htie
  exact ⟨key, hinj, fun t => (hcut _).symm.le.trans (hkey t)⟩

/-- A matching-cost bound at every threshold controls all prefixes of one ordering,
including prefixes that split equal optimized keys. -/
theorem exists_key_of_matchingCost (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2) (score : Sym2 V → ℝ)
    {d B T : ℕ} (hd : 2 ≤ d) (degree : ∀ v, H.degree v ≤ d)
    (htie : ∀ a, (H.edgeFinset.filter fun e => score e = a).card ≤ T)
    (hbound : ∀ t, matchingCost H M stars pairs (fun e => belowThreshold t (score e)) ≤ B) :
    ∃ key : V → ℕ, Function.Injective key ∧
      ∀ t, (H.cutFinset (univ.filter fun v => key v < t)).card ≤
        B + d * (T * (2 * d ^ 2)) := by
  apply exists_key_of_threshold_bounds H (matchingKey H M stars pairs score) degree
  · intro t
    exact (card_cut_matchingKey_le H M hM hdisj stars pairs score t).trans (hbound t)
  · exact card_matchingKey_ties_le H M hM hdisj stars pairs score hd degree htie

end Frontier.PairLayout

