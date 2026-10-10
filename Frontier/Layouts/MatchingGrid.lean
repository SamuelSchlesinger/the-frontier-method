/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.MatchingLocal

/-!
# A finite grid controls every matching-layout prefix

Sorting the optimized keys is safe even when keys coincide. Each key is an
actual nearby edge score, so a bounded source load transfers edge windows and
tails to vertex windows and tails. The grid estimate includes every prefix
that splits a tie group.
-/

@[expose] public section

namespace Frontier.PairLayout

open Finset Gaussian

variable {V : Type} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]

omit [DecidableEq V] in
/-- The score-grid argument for arbitrary bounded-degree simple graphs. -/
theorem card_cut_le_vertex_grid {d : ℕ} (degree : ∀ v, H.degree v ≤ d) (score : V → ℝ)
    (P : Finset V) {m a δ : ℝ} (hP : ∀ v ∈ P, score v ≤ m)
    (hPc : ∀ v ∉ P, m ≤ score v) (hδ : 0 < δ) (N : ℕ) {B : ℝ}
    (low : d * (#{v | score v < a} : ℝ) ≤ B)
    (high : d * (#{v | a + N * δ ≤ score v} : ℝ) ≤ B)
    (mid : ∀ i < N, ((H.cutFinset {v | score v < a + i * δ}).card : ℝ) +
      d * #{v | a + i * δ ≤ score v ∧ score v < a + (i + 1) * δ} ≤ B) :
    ((H.cutFinset P).card : ℝ) ≤ B := by
  classical
  let touching := fun S : Finset V => S.biUnion (fun v => H.incidenceFinset v)
  have count (S : Finset V) (hsub : H.cutFinset P ⊆ touching S) :
      ((H.cutFinset P).card : ℝ) ≤ d * S.card := by
    exact_mod_cast (card_le_card hsub).trans (card_incidence_biUnion_le degree S)
  have touch {e : Sym2 V} (he : e ∈ H.edgeSet) {u v : V} {S : Finset V}
      (huv : e = s(u, v)) (hu : u ∈ S) : e ∈ touching S :=
    mem_biUnion.mpr ⟨u, hu, SimpleGraph.mem_incidenceFinset.mpr ⟨he, by simp [huv]⟩⟩
  by_cases hlo : m < a
  · apply (count {v | score v < a} ?_).trans low
    intro e he
    obtain ⟨he, u, v, huv, hu, _⟩ := SimpleGraph.mem_cutFinset.mp he
    exact touch he huv (mem_filter.mpr ⟨mem_univ _, (hP u hu).trans_lt hlo⟩)
  by_cases hhi : a + N * δ ≤ m
  · apply (count {v | a + N * δ ≤ score v} ?_).trans high
    intro e he
    obtain ⟨he, u, v, huv, _, hv⟩ := SimpleGraph.mem_cutFinset.mp he
    exact touch he (huv.trans Sym2.eq_swap) (mem_filter.mpr
      ⟨mem_univ _, hhi.trans (hPc v hv)⟩)
  obtain ⟨i, hi, ht, ht'⟩ := exists_grid_index hδ (M := N) (not_lt.mp hlo) (not_le.mp hhi)
  let window : Finset V := {v | a + i * δ ≤ score v ∧ score v < a + (i + 1) * δ}
  have hsub : H.cutFinset P ⊆ H.cutFinset {v | score v < a + i * δ} ∪ touching window := by
    intro e he
    obtain ⟨he, u, v, huv, hu, hv⟩ := SimpleGraph.mem_cutFinset.mp he
    by_cases hut : score u < a + i * δ
    · apply mem_union_left
      exact SimpleGraph.mem_cutFinset.mpr ⟨he, u, v, huv,
        mem_filter.mpr ⟨mem_univ _, hut⟩,
        fun h => not_lt_of_ge (ht.trans (hPc v hv)) (mem_filter.mp h).2⟩
    · apply mem_union_right
      exact touch he huv (mem_filter.mpr ⟨mem_univ _, le_of_not_gt hut,
        (hP u hu).trans_lt ht'⟩)
  have hb := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_left (card_incidence_biUnion_le degree window) _))
  have hr : ((H.cutFinset P).card : ℝ) ≤
      (H.cutFinset {v | score v < a + i * δ}).card + d * window.card := by exact_mod_cast hb
  exact hr.trans (by simpa only [window, Nat.cast_add, Nat.cast_one] using mid i hi)

omit [DecidableEq V] in
/-- Sorting a real key and bounding finite grid windows controls all prefixes. -/
theorem exists_key_of_vertex_grid {d : ℕ} (degree : ∀ v, H.degree v ≤ d) (score : V → ℝ)
    {a δ : ℝ} (hδ : 0 < δ) (N : ℕ) {B : ℝ}
    (low : d * (#{v | score v < a} : ℝ) ≤ B)
    (high : d * (#{v | a + N * δ ≤ score v} : ℝ) ≤ B)
    (mid : ∀ i < N, ((H.cutFinset {v | score v < a + i * δ}).card : ℝ) +
      d * #{v | a + i * δ ≤ score v ∧ score v < a + (i + 1) * δ} ≤ B) :
    ∃ key : V → ℕ, Function.Injective key ∧ ∀ t,
      ((H.cutFinset {v | key v < t}).card : ℝ) ≤ B := by
  classical
  obtain ⟨key, hinj, hkey⟩ := exists_key_of_score score
  refine ⟨key, hinj, fun t => ?_⟩
  rcases hkey t with hempty | ⟨m, hP, hPc⟩
  · have hB : 0 ≤ B := le_trans (by positivity) low
    have he : ({v | key v < t} : Finset V) = ∅ := filter_eq_empty_iff.mpr fun v _ => hempty v
    simpa [he, SimpleGraph.cutFinset] using hB
  · exact card_cut_le_vertex_grid H degree score _
      (fun v hv => hP v (mem_filter.mp hv).2)
      (fun v hv => hPc v fun h => hv (mem_filter.mpr ⟨mem_univ _, h⟩)) hδ N low high mid

/-- Any property of selected keys is paid for by nearby source edges. -/
theorem card_matchingKey_filter_le (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2) (score : Sym2 V → ℝ)
    {d : ℕ} (hd : 2 ≤ d) (degree : ∀ v, H.degree v ≤ d)
    (p : ℝ → Prop) [DecidablePred p] :
    (univ.filter fun v => p (matchingKey H M stars pairs score v)).card ≤
      2 * d ^ 2 * (H.edgeFinset.filter fun e => p (score e)).card := by
  let sources := H.edgeFinset.filter fun e => p (score e)
  have hsub : (univ.filter fun v => p (matchingKey H M stars pairs score v)) ⊆
      sources.biUnion (edgeSupport H 1) := by
    intro v hv
    obtain ⟨e, he, hv', hk⟩ := matchingKey_source H M hM hdisj stars pairs score v
    exact mem_biUnion.mpr ⟨e, mem_filter.mpr ⟨he, hk ▸ (mem_filter.mp hv).2⟩, hv'⟩
  calc
    _ ≤ (sources.biUnion (edgeSupport H 1)).card := card_le_card hsub
    _ ≤ ∑ e ∈ sources, (edgeSupport H 1 e).card := card_biUnion_le
    _ ≤ ∑ _e ∈ sources, 2 * d ^ 2 := sum_le_sum fun e _ => card_edgeSupport_one_le H hd degree e
    _ = _ := by simp [sources, Nat.mul_comm]

/-- Grid costs and edge-score windows yield one ordering with no distinct-score assumption. -/
theorem exists_key_of_matching_grid (regular : H.IsRegularOfDegree 3)
    (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2) (score : Sym2 V → ℝ)
    {a δ : ℝ} (hδ : 0 < δ) (N : ℕ) {B : ℝ}
    (low : 54 * (#{e ∈ H.edgeFinset | score e < a} : ℝ) ≤ B)
    (high : 54 * (#{e ∈ H.edgeFinset | a + N * δ ≤ score e} : ℝ) ≤ B)
    (mid : ∀ i < N,
      (matchingCost H M stars pairs (fun e => belowThreshold (a + i * δ) (score e)) : ℝ) +
        54 * #{e ∈ H.edgeFinset | a + i * δ ≤ score e ∧ score e < a + (i + 1) * δ} ≤ B) :
    ∃ key : V → ℕ, Function.Injective key ∧ ∀ t,
      ((H.cutFinset {v | key v < t}).card : ℝ) ≤ B := by
  classical
  have degree : ∀ v, H.degree v ≤ 3 := fun v => (regular.degree_eq v).le
  have count (p : ℝ → Prop) [DecidablePred p] :
      ((univ.filter fun v => p (matchingKey H M stars pairs score v)).card : ℝ) ≤
        18 * (H.edgeFinset.filter fun e => p (score e)).card := by
    exact_mod_cast card_matchingKey_filter_le H M hM hdisj stars pairs score
      (by norm_num : 2 ≤ 3) degree p
  apply exists_key_of_vertex_grid H degree (matchingKey H M stars pairs score) hδ N
  · have := count (· < a)
    norm_num only [Nat.cast_ofNat]
    linarith
  · have := count (a + N * δ ≤ ·)
    norm_num only [Nat.cast_ofNat]
    linarith
  · intro i hi
    have hw := count (fun x => a + i * δ ≤ x ∧ x < a + (i + 1) * δ)
    have hc : ((H.cutFinset {v | matchingKey H M stars pairs score v < a + i * δ}).card : ℝ) ≤
        matchingCost H M stars pairs (fun e => belowThreshold (a + i * δ) (score e)) := by
      exact_mod_cast card_cut_matchingKey_le H M hM hdisj stars pairs score (a + i * δ)
    norm_num only [Nat.cast_ofNat]
    linarith [mid i hi]

end Frontier.PairLayout
