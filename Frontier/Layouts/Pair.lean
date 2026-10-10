/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.GaussianPatch
public import Frontier.Layouts.Local
public import Frontier.Layouts.Patch

/-!
# Realizing the two-vertex port cost in one ordering

The four colors in `Gaussian.twoVertexCost` belong to edge scores, not to the
neighboring vertex keys. They can nevertheless bound the original graph cut:
subdivide every edge outside a chosen set, give its new midpoint the edge-score
color, and use the triangle inequality for Boolean disagreement. Edges inside a
two-vertex patch stay unsubdivided.

The explicit key `pairKey` attains the two-vertex minimum at every threshold of
one ordering. It always selects one of the four outer scores, so local load
bounds on these choices control ties. The final theorem transfers any uniform
port-cost estimate to all prefixes, including the necessary tie overhead.

These deterministic results do not supply the missing uniform probabilistic
estimate or the target quarter coefficient.
-/

@[expose] public section

namespace Frontier.PairLayout

open Gaussian

/-- The first vertex key in a pair. Swap the two outer pairs for the second key. -/
def pairKey (a b c d : ℝ) : ℝ :=
  min (max a b) (max (min a b) (min c d))

/-- The largest minimum-cut choice is monotone in the four boundary colors. -/
def pairColor (a b c d : Bool) : Bool :=
  (a && b) || ((a || b) && (c || d))

/-- Thresholding the single real key gives the optimal Boolean choice at every threshold. -/
theorem belowThreshold_pairKey (a b c d t : ℝ) :
    belowThreshold t (pairKey a b c d) =
      pairColor (belowThreshold t a) (belowThreshold t b)
        (belowThreshold t c) (belowThreshold t d) := by
  classical
  by_cases ha : a < t <;> by_cases hb : b < t <;>
    by_cases hc : c < t <;> by_cases hd : d < t <;>
    simp [belowThreshold, pairKey, pairColor, min_lt_iff, max_lt_iff, ha, hb, hc, hd]

/-- Both chosen colors attain the patch minimum. -/
theorem twoVertexEnergy_pairColor (a b c d : Bool) :
    twoVertexEnergy a b c d (pairColor a b c d) (pairColor c d a b) =
      twoVertexCost a b c d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

/-- One pair of real keys attains all threshold minima, with no independent choices of cuts. -/
theorem twoVertexEnergy_pairKey (a b c d t : ℝ) :
    twoVertexEnergy (belowThreshold t a) (belowThreshold t b)
      (belowThreshold t c) (belowThreshold t d)
      (belowThreshold t (pairKey a b c d)) (belowThreshold t (pairKey c d a b)) =
      twoVertexCost (belowThreshold t a) (belowThreshold t b)
        (belowThreshold t c) (belowThreshold t d) := by
  simp only [belowThreshold_pairKey, twoVertexEnergy_pairColor]

/-- A pair key is one of its four outer edge scores. -/
theorem pairKey_mem (a b c d : ℝ) :
    pairKey a b c d = a ∨ pairKey a b c d = b ∨
      pairKey a b c d = c ∨ pairKey a b c d = d := by
  unfold pairKey
  rcases min_choice (max a b) (max (min a b) (min c d)) with h | h
  · rw [h]
    rcases max_choice a b with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rw [h]
    rcases max_choice (min a b) (min c d) with h | h
    · rw [h]
      rcases min_choice a b with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rw [h]
      rcases min_choice c d with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))

/-- A cubic star costs one exactly when its edge colors straddle. -/
def starCost (a b c : Bool) : ℕ := if a = b ∧ b = c then 0 else 1

/-- Removing the constrained midpoint of the central edge never increases the two-star cost.
This compares the patch objective with the original edge-score straddling objective. -/
theorem twoVertexCost_le_starCost (a b c d e : Bool) :
    twoVertexCost a b c d ≤ starCost a b e + starCost c d e := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

end Frontier.PairLayout

namespace Frontier.Multigraph

open Finset Gaussian

variable {V E : Type*} [Fintype E] (G : Multigraph V E)

/-- Keep the edges of `M` intact and subdivide all others at fixed port colors.
Each subdivided edge pays for both endpoint-to-port disagreements. -/
noncomputable def portCut (M : Finset E) (port : E → Bool) (color : V → Bool) : ℕ := by
  classical
  exact ∑ e, if e ∈ M then G.crossing color e else
    portDisagreement (color (G.src e)) (port e) +
      portDisagreement (color (G.tgt e)) (port e)

/-- The half-edge costs at a vertex outside the intact edge set. Source and target
occurrences are counted separately, so this definition also handles loops. -/
noncomputable def outerPortCost (M : Finset E) (port : E → Bool)
    (color : V → Bool) (v : V) : ℕ := by
  classical
  exact ∑ e, if e ∈ M then 0 else
    (if G.src e = v then portDisagreement (color v) (port e) else 0) +
      (if G.tgt e = v then portDisagreement (color v) (port e) else 0)

/-- The auxiliary cut decomposes exactly into intact edges and vertex half-edge costs. -/
theorem portCut_eq_outerPortCost [Fintype V]
    (M : Finset E) (port : E → Bool) (color : V → Bool) :
    G.portCut M port color = (∑ e ∈ M, G.crossing color e) +
      ∑ v, G.outerPortCost M port color v := by
  classical
  have hsum : (∑ v, G.outerPortCost M port color v) =
      ∑ e, if e ∈ M then 0 else
        portDisagreement (color (G.src e)) (port e) +
          portDisagreement (color (G.tgt e)) (port e) := by
    simp only [outerPortCost]
    rw [sum_comm]
    apply sum_congr rfl
    intro e _
    by_cases he : e ∈ M <;> simp [he, sum_add_distrib]
  have hM : (∑ e ∈ M, G.crossing color e) =
      ∑ e, if e ∈ M then G.crossing color e else 0 := by
    rw [← sum_filter]
    congr 1
    ext e
    simp
  rw [hsum, hM, portCut, ← sum_add_distrib]
  apply sum_congr rfl
  intro e _
  by_cases he : e ∈ M <;> simp [he]

/-- Regrouping a vertex partition into singles and pairs charges every external half-edge
once and every selected internal edge once. No independence of adjacent patches is assumed. -/
theorem portCut_eq_blocks {S P : Type*} [Fintype S] [Fintype P]
    (M : Finset E) (port : E → Bool) (color : V → Bool)
    (vertices : (S ⊕ (P × Bool)) ≃ V) (internal : P ≃ ↥M) :
    G.portCut M port color =
      (∑ s, G.outerPortCost M port color (vertices (.inl s))) +
      ∑ p, (G.crossing color (internal p) +
        G.outerPortCost M port color (vertices (.inr (p, false))) +
        G.outerPortCost M port color (vertices (.inr (p, true)))) := by
  let _ := Fintype.ofEquiv (S ⊕ (P × Bool)) vertices
  rw [G.portCut_eq_outerPortCost]
  have hi : (∑ e ∈ M, G.crossing color e) = ∑ p, G.crossing color (internal p) := by
    rw [← sum_coe_sort]
    exact (internal.sum_comp (fun e => G.crossing color e)).symm
  have hv := vertices.sum_comp (G.outerPortCost M port color)
  rw [← hv, hi]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, sum_add_distrib]
  lia

/-- Every original crossing is paid for by its intact edge or by a subdivided half-edge.
No matching, independence, or probability hypothesis is required for this comparison. -/
theorem cutSize_le_portCut (M : Finset E) (port : E → Bool) (color : V → Bool) :
    G.cutSize color ≤ G.portCut M port color := by
  classical
  apply sum_le_sum
  intro e _
  by_cases he : e ∈ M
  · simp [he]
  · simp only [he, ite_false]
    cases hs : color (G.src e) <;> cases ht : color (G.tgt e) <;> cases hp : port e <;>
      simp [crossing, portDisagreement, hs, ht]

/-- The port comparison bounds the ordinary threshold cut. -/
theorem ncard_cut_le_portCut (M : Finset E) (edgeKey : E → ℝ) (key : V → ℝ) (t : ℝ) :
    (G.cut {v | key v < t}).ncard ≤
      G.portCut M (fun e => belowThreshold t (edgeKey e))
        (fun v => belowThreshold t (key v)) := by
  have h := G.cutSize_le_portCut M (fun e => belowThreshold t (edgeKey e))
    (fun v => belowThreshold t (key v))
  simpa [cutSize_eq_ncard, belowThreshold] using h

end Frontier.Multigraph

namespace Frontier.PairLayout

open Finset Gaussian

variable {V E : Type*} [Fintype V] [Fintype E]

open Classical in
/-- Selecting keys from a different finite source type multiplies its tie bound only by
the number of vertices that can select each source. -/
theorem card_ties_le_of_sources (edgeKey : E → ℝ) (key : V → ℝ) (scope : V → Finset E)
    {M L : ℕ} (hlocal : ∀ v, ∃ e ∈ scope v, key v = edgeKey e)
    (hload : ∀ e, (univ.filter fun v => e ∈ scope v).card ≤ L)
    (htie : ∀ a, (univ.filter fun e => edgeKey e = a).card ≤ M) (a : ℝ) :
    (univ.filter fun v => key v = a).card ≤ M * L := by
  classical
  let sources := univ.filter fun e => edgeKey e = a
  have hsub : univ.filter (fun v => key v = a) ⊆
      sources.biUnion (fun e => univ.filter fun v => e ∈ scope v) := by
    intro v hv
    obtain ⟨e, he, hk⟩ := hlocal v
    exact mem_biUnion.mpr ⟨e, mem_filter.mpr ⟨mem_univ _,
      hk.symm.trans (mem_filter.mp hv).2⟩, mem_filter.mpr ⟨mem_univ _, he⟩⟩
  calc (univ.filter fun v => key v = a).card
      ≤ (sources.biUnion fun e => univ.filter fun v => e ∈ scope v).card := card_le_card hsub
    _ ≤ ∑ e ∈ sources, (univ.filter fun v => e ∈ scope v).card := card_biUnion_le
    _ ≤ ∑ _e ∈ sources, L := sum_le_sum fun e _ => hload e
    _ = sources.card * L := by simp
    _ ≤ M * L := Nat.mul_le_mul_right L (htie a)

open Classical in
/-- A uniform port-cost bound supplies a single injective ordering. The extra term pays
for prefixes that split a group of equal selected keys, rather than ignoring those ties. -/
theorem exists_key_of_portCut (G : Multigraph V E) (M : Finset E)
    (edgeKey : E → ℝ) (key : V → ℝ) (scope : V → Finset E) {d B T L : ℕ}
    (hdegree : G.MaxDegreeLE d)
    (hlocal : ∀ v, ∃ e ∈ scope v, key v = edgeKey e)
    (hload : ∀ e, (univ.filter fun v => e ∈ scope v).card ≤ L)
    (htie : ∀ a, (univ.filter fun e => edgeKey e = a).card ≤ T)
    (hbound : ∀ t, G.portCut M (fun e => belowThreshold t (edgeKey e))
      (fun v => belowThreshold t (key v)) ≤ B) :
    ∃ order : V → ℕ, Function.Injective order ∧
      ∀ t, (G.cut {v | order v < t}).ncard ≤ B + d * (T * L) := by
  classical
  let H : Hypergraph V E := fun e => {G.src e, G.tgt e}
  have hcut (X : Set V) : H.cut X = G.cut X := by
    ext e
    simp only [Hypergraph.cut, H, Set.mem_ofPred_eq, Set.nonempty_def,
      Set.mem_inter_iff, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff,
      Multigraph.mem_cut]
    by_cases hs : G.src e ∈ X <;> by_cases ht : G.tgt e ∈ X <;> aesop
  suffices h : ∃ order : V → ℕ, Function.Injective order ∧
      ∀ t, (H.cut {v | order v < t}).ncard ≤ B + d * (T * L) by
    simpa only [hcut] using h
  apply H.exists_key_cut_le key
  · intro v
    simpa [H, Multigraph.edgesAt, Multigraph.Incident, eq_comm] using hdegree v
  · intro t
    rw [hcut]
    exact (G.ncard_cut_le_portCut M edgeKey key t).trans (hbound t)
  · exact card_ties_le_of_sources edgeKey key scope hlocal hload htie

end Frontier.PairLayout
