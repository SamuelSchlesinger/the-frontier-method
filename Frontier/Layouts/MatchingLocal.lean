/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.MatchingMean

/-!
# Local events for the matching cost

Assign each pair's cost to its first endpoint and zero to the other; singleton
costs remain at their vertices. Each contribution is at most two and depends
only on Gaussian coordinates within radius `R+2`. Two indicators per vertex
then express the entire matching cost, making the existing second-moment
concentration theorem applicable without any independence assumption between
overlapping patches.
-/

@[expose] public section

namespace Frontier.PairLayout

open Finset Gaussian MeasureTheory

variable {V : Type} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]

omit [DecidableRel H.Adj] in
/-- Every vertex is either a singleton or an endpoint slot of the matching. -/
theorem single_or_pairEndpoint (M : Finset (Sym2 V)) (v : V) :
    v ∈ singleVertices M ∨ ∃ x : ↥M × Bool, pairEndpoint M x = v := by
  by_cases hv : v ∈ singleVertices M
  · exact Or.inl hv
  · right
    have hv' : v ∈ matchedVertices M := by simpa [singleVertices] using hv
    obtain ⟨e, he, hv⟩ := mem_biUnion.mp hv'
    have ho : e.toFinset = {e.out.1, e.out.2} := by
      conv_lhs => rw [← Sym2.mk_fst_out_snd_out e]
      exact Sym2.toFinset_mk_eq
    rw [ho, mem_insert, mem_singleton] at hv
    rcases hv with h | h
    · exact ⟨(⟨e, he⟩, false), h.symm⟩
    · exact ⟨(⟨e, he⟩, true), h.symm⟩

/-- Charge the cost of each pair to its first endpoint. -/
noncomputable def matchingVertexCost (M : Finset (Sym2 V))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2) (port : Sym2 V → Bool) : V → ℕ :=
  Function.extend (pairEndpoint M)
    (fun x => if x.2 then 0 else
      twoVertexCost (port ((pairs x.1).outerEdges 0)) (port ((pairs x.1).outerEdges 1))
        (port ((pairs x.1).outerEdges 2)) (port ((pairs x.1).outerEdges 3)))
    (fun v => starCost (port s(v, (stars v 0).val))
      (port s(v, (stars v 1).val)) (port s(v, (stars v 2).val)))

omit [DecidableRel H.Adj] in
theorem matchingVertexCost_single (M : Finset (Sym2 V))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2) (port : Sym2 V → Bool)
    {v : V} (hv : v ∈ singleVertices M) :
    matchingVertexCost H M stars pairs port v =
      starCost (port s(v, (stars v 0).val)) (port s(v, (stars v 1).val))
        (port s(v, (stars v 2).val)) := by
  apply Function.extend_apply'
  rintro ⟨x, hx⟩
  exact (mem_sdiff.mp hv).2 (mem_biUnion.mpr
    ⟨x.1.val, x.1.property, hx ▸ pairEndpoint_mem M x⟩)

theorem matchingVertexCost_pair (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2) (port : Sym2 V → Bool)
    (x : ↥M × Bool) :
    matchingVertexCost H M stars pairs port (pairEndpoint M x) =
      if x.2 then 0 else twoVertexCost
        (port ((pairs x.1).outerEdges 0)) (port ((pairs x.1).outerEdges 1))
        (port ((pairs x.1).outerEdges 2)) (port ((pairs x.1).outerEdges 3)) :=
  (pairEndpoint_injective H M hM hdisj).extend_apply _ _ x

theorem sum_matchingVertexCost (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2) (port : Sym2 V → Bool) :
    ∑ v, matchingVertexCost H M stars pairs port v = matchingCost H M stars pairs port := by
  rw [sum_vertices_eq_matching_blocks H M hM hdisj, matchingCost]
  congr 1
  · exact sum_congr rfl fun v hv => matchingVertexCost_single H M stars pairs port hv
  · rw [← sum_coe_sort M]
    apply sum_congr rfl
    intro e _
    have hl := matchingVertexCost_pair H M hM hdisj stars pairs port (e, false)
    have hr := matchingVertexCost_pair H M hM hdisj stars pairs port (e, true)
    simpa only [pairEndpoint, Bool.false_eq_true, ite_false, ite_true, hl, hr, add_zero] using
      congrArg₂ (· + ·) hl hr

theorem matchingVertexCost_le_two (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2) (port : Sym2 V → Bool) (v : V) :
    matchingVertexCost H M stars pairs port v ≤ 2 := by
  rcases single_or_pairEndpoint M v with hv | ⟨x, rfl⟩
  · rw [matchingVertexCost_single H M stars pairs port hv]
    unfold starCost
    split_ifs <;> decide
  · rw [matchingVertexCost_pair H M hM hdisj stars pairs port x]
    split_ifs
    · decide
    · generalize port ((pairs x.1).outerEdges 0) = a, port ((pairs x.1).outerEdges 1) = b,
        port ((pairs x.1).outerEdges 2) = c, port ((pairs x.1).outerEdges 3) = d
      cases a <;> cases b <;> cases c <;> cases d <;> decide

omit [DecidableRel H.Adj] in
/-- Every outer edge score is supported in the radius-`R+2` ball at either center. -/
theorem CubicPair.outerSupport_subset {u v : V} (p : CubicPair H u v) (R : ℕ) (i : Fin 4) :
    edgeSupport H R (p.outerEdges i) ⊆ ball H u (R + 2) ∧
      edgeSupport H R (p.outerEdges i) ⊆ ball H v (R + 2) := by
  classical
  have hl (j : Fin 3) : edgeSupport H R s(u, (p.leftNeighbors j).val) ⊆ ball H u (R + 1) :=
    edgeSupport_subset_ball (CubicPair.incidenceEnum p.leftNeighbors j).property
  have hr (j : Fin 3) : edgeSupport H R s(v, (p.rightNeighbors j).val) ⊆ ball H v (R + 1) :=
    edgeSupport_subset_ball (CubicPair.incidenceEnum p.rightNeighbors j).property
  have huv := ball_subset_ball_of_adj H p.adjacent (R + 1)
  have hvu := ball_subset_ball_of_adj H p.adjacent.symm (R + 1)
  have hu := ball_mono H u (show R + 1 ≤ R + 2 by lia)
  have hv := ball_mono H v (show R + 1 ≤ R + 2 by lia)
  fin_cases i
  · exact ⟨(hl 1).trans hu, (hl 1).trans hvu⟩
  · exact ⟨(hl 2).trans hu, (hl 2).trans hvu⟩
  · exact ⟨(hr 1).trans huv, (hr 1).trans hv⟩
  · exact ⟨(hr 2).trans huv, (hr 2).trans hv⟩

theorem measurable_matchingVertexCost (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2) (q : ℝ) (R : ℕ) (t : ℝ) (v : V) :
    Measurable (fun ω => (matchingVertexCost H M stars pairs
      (fun e => belowThreshold t (edgeScore H q R ω e)) v : ℝ)) := by
  rcases single_or_pairEndpoint M v with hv | ⟨x, rfl⟩
  · simp only [matchingVertexCost_single H M stars pairs _ hv, starCost_eq_straddle,
      Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact Measurable.ite (measurableSet_straddleEvent q R t v) measurable_const measurable_const
  · simp only [matchingVertexCost_pair H M hM hdisj stars pairs _ x]
    cases hx : x.2
    · simpa only [hx, Bool.false_eq_true, ite_false, Function.comp_def,
        twoVertexThresholdCost] using
        (measurable_twoVertexThresholdCost t).comp
          (Measurable.of_eval fun i => measurable_edgeScore H q R ((pairs x.1).outerEdges i))
    · simpa only [hx, ite_true, Nat.cast_zero] using
        (measurable_const : Measurable (fun _ : V → ℝ => (0 : ℝ)))

theorem dependsOn_matchingVertexCost (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2) (q : ℝ) (R : ℕ) (t : ℝ) (v : V) :
    DependsOn (fun ω => matchingVertexCost H M stars pairs
      (fun e => belowThreshold t (edgeScore H q R ω e)) v) (ball H v (R + 2) : Set V) := by
  intro ω ω' h
  rcases single_or_pairEndpoint M v with hv | ⟨x, rfl⟩
  · simp only [matchingVertexCost_single H M stars pairs _ hv]
    have hs (i : Fin 3) : edgeScore H q R ω s(v, (stars v i).val) =
        edgeScore H q R ω' s(v, (stars v i).val) :=
      edgeScore_congr
        ((edgeSupport_subset_ball (CubicPair.incidenceEnum (stars v) i).property).trans
          (ball_mono H v (show R + 1 ≤ R + 2 by lia))) fun z hz => h z hz
    rw [hs 0, hs 1, hs 2]
  · simp only [matchingVertexCost_pair H M hM hdisj stars pairs _ x]
    cases hx : x.2
    · have hs (i : Fin 4) : edgeScore H q R ω ((pairs x.1).outerEdges i) =
          edgeScore H q R ω' ((pairs x.1).outerEdges i) :=
        edgeScore_congr (((pairs x.1).outerSupport_subset H R i).1) fun z hz => by
          apply h z
          simpa only [pairEndpoint, hx, Bool.false_eq_true, ite_false, Finset.mem_coe] using hz
      simp only [hs]
    · simp only [ite_true]

/-- The first and second unit of cost at a vertex are separate local events. -/
def matchingCostEvent (M : Finset (Sym2 V))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2)
    (q : ℝ) (R : ℕ) (t : ℝ) (x : V × Fin 2) : Set (V → ℝ) :=
  {ω | (x.2.val : ℝ) + 1 ≤ (matchingVertexCost H M stars pairs
    (fun e => belowThreshold t (edgeScore H q R ω e)) x.1 : ℝ)}

theorem measurableSet_matchingCostEvent (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2)
    (q : ℝ) (R : ℕ) (t : ℝ) (x : V × Fin 2) :
    MeasurableSet (matchingCostEvent H M stars pairs q R t x) :=
  measurableSet_le measurable_const
    (measurable_matchingVertexCost H M hM hdisj stars pairs q R t x.1)

theorem dependsOn_matchingCostEvent (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2)
    (q : ℝ) (R : ℕ) (t : ℝ) (x : V × Fin 2) :
    DependsOn (· ∈ matchingCostEvent H M stars pairs q R t x)
      (ball H x.1 (R + 2) : Set V) := by
  intro ω ω' h
  simp only [matchingCostEvent, Set.mem_ofPred_eq]
  exact congrArg (fun n : ℕ => (x.2.val : ℝ) + 1 ≤ (n : ℝ))
    (dependsOn_matchingVertexCost H M hM hdisj stars pairs q R t x.1 h)

/-- The sum of the local unit indicators is exactly the total matching cost. -/
theorem matchingCost_eq_sum_indicators (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2)
    (q : ℝ) (R : ℕ) (t : ℝ) (ω : V → ℝ) :
    (matchingCost H M stars pairs (fun e => belowThreshold t (edgeScore H q R ω e)) : ℝ) =
      ∑ x : V × Fin 2, (matchingCostEvent H M stars pairs q R t x).indicator 1 ω := by
  classical
  rw [← sum_matchingVertexCost H M hM hdisj stars pairs, Nat.cast_sum, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro v _
  have hn := matchingVertexCost_le_two H M hM hdisj stars pairs
    (fun e => belowThreshold t (edgeScore H q R ω e)) v
  simp only [matchingCostEvent, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
  generalize matchingVertexCost H M stars pairs
    (fun e => belowThreshold t (edgeScore H q R ω e)) v = n at hn ⊢
  rw [Fin.sum_univ_two]
  interval_cases n <;> norm_num

theorem sum_measure_matchingCostEvent (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2)
    (q : ℝ) (R : ℕ) (t : ℝ) :
    (∑ x : V × Fin 2, (gaussPi V).real (matchingCostEvent H M stars pairs q R t x)) =
      ∫ ω, (matchingCost H M stars pairs
        (fun e => belowThreshold t (edgeScore H q R ω e)) : ℝ) ∂gaussPi V := by
  let A := matchingCostEvent H M stars pairs q R t
  have hm := measurableSet_matchingCostEvent H M hM hdisj stars pairs q R t
  have hi (x) : Integrable ((A x).indicator (1 : (V → ℝ) → ℝ)) (gaussPi V) :=
    (integrable_const 1).indicator (hm x)
  calc
    _ = ∑ x : V × Fin 2, ∫ ω, (A x).indicator 1 ω ∂gaussPi V :=
      sum_congr rfl fun x _ => (integral_indicator_one (hm x)).symm
    _ = ∫ ω, ∑ x : V × Fin 2, (A x).indicator 1 ω ∂gaussPi V :=
      (integral_finsetSum _ fun x _ => hi x).symm
    _ = _ := integral_congr_ae (ae_of_all _ fun ω =>
      (matchingCost_eq_sum_indicators H M hM hdisj stars pairs q R t ω).symm)

/-- The matching cost has an `O(h/c²)` deviation bound. The constant depends only
on the fixed kernel radius, not on the graph, matching, or threshold. -/
theorem measureReal_matchingCost_deviation_le (regular : H.IsRegularOfDegree 3)
    (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2)
    (q : ℝ) (R : ℕ) (t : ℝ) {c : ℝ} (hc : 0 < c) :
    (gaussPi V).real {ω |
      c ≤ |(matchingCost H M stars pairs
          (fun e => belowThreshold t (edgeScore H q R ω e)) : ℝ) -
        ∫ ω', (matchingCost H M stars pairs
          (fun e => belowThreshold t (edgeScore H q R ω' e)) : ℝ) ∂gaussPi V|} ≤
      4 * Fintype.card V * vertexOverlap 3 (R + 2) / c ^ 2 := by
  classical
  have degree : ∀ v, H.degree v ≤ 3 := fun v => (regular.degree_eq v).le
  let A := matchingCostEvent H M stars pairs q R t
  have overlap (x : V × Fin 2) :
      (univ.filter fun y : V × Fin 2 =>
        ¬ Disjoint (ball H x.1 (R + 2)) (ball H y.1 (R + 2))).card ≤
          vertexOverlap 3 (R + 2) * 2 := by
    have heq : (univ.filter fun y : V × Fin 2 =>
        ¬ Disjoint (ball H x.1 (R + 2)) (ball H y.1 (R + 2))) =
      (univ.filter fun w => ¬ Disjoint (ball H x.1 (R + 2)) (ball H w (R + 2))) ×ˢ
        (univ : Finset (Fin 2)) := by ext y; simp
    rw [heq, card_product, card_univ, Fintype.card_fin]
    exact Nat.mul_le_mul_right 2 (ball_overlap_le H (by norm_num) degree (R + 2) x.1)
  have hp := pi_deviation_le (fun _ : V => ProbabilityTheory.gaussianReal 0 1) univ A
    (fun x => ball H x.1 (R + 2))
    (fun x _ => measurableSet_matchingCostEvent H M hM hdisj stars pairs q R t x)
    (fun x _ => dependsOn_matchingCostEvent H M hM hdisj stars pairs q R t x)
    (fun x _ => overlap x) hc
  have hmean := sum_measure_matchingCostEvent H M hM hdisj stars pairs q R t
  have hcost := matchingCost_eq_sum_indicators H M hM hdisj stars pairs q R t
  change (gaussPi V).real {ω | c ≤ |∑ x, (A x).indicator 1 ω -
    ∑ x, (gaussPi V).real (A x)|} ≤ _ at hp
  dsimp only [A] at hp
  simp_rw [← hcost, hmean] at hp
  convert hp using 1
  simp only [card_univ, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
  ring

end Frontier.PairLayout
