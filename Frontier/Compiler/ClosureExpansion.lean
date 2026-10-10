/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Compiler.Closure

/-!
# Expanding a semantic block layout

A bound on the closed one-source hypergraph gives a bound on realized patterns
in the original circuit graph, with logarithmic overhead for the one partially
processed block. Additional chosen edges, including the edges incident to the
vertex being processed, are charged explicitly. The bound holds on any input
set, so it applies in particular to charged transitions.
-/

@[expose] public section

namespace Frontier.Compiler

open Cslib.Circuits Set

variable {σ : Signature} {n s : ℕ} {O : Type*} [Finite O]
  (p : Program σ n s) (out : O → Wire n s)
  (I : Interpretation σ Bool) (Acc : O → Set Bool) {d : ℕ}
  (c : Multigraph.Compression (network p out I Acc).toMultigraph d)

/-- A semantic block layout expands to a single physical layout. Every chosen
input set has few patterns on a frontier together with any additional edges. -/
theorem exists_layout_oneSource_patterns {key : c.blocks → ℕ} (hkey : key.Injective)
    {w : ℕ} (hw : ∀ q, ((oneSourceHypergraph p out I Acc c).cut {B | key B < q}).ncard ≤ w) :
    ∃ π : Layout (Vertex p out), ∀ t (S : Set (Fin n → Bool)) (R : Set (Edge p out)),
      ((fun x (e : ↥((network p out I Acc).frontier π t ∪ R)) =>
        p.trace I x e.val.signal.val) '' S).ncard ≤
        2 ^ (w + d * Nat.log 2 (Nat.card (Vertex p out)) + d + R.ncard) := by
  classical
  let N := network p out I Acc
  obtain ⟨π, hπ⟩ := c.exists_layout_prefixes hkey
  refine ⟨π, fun t S R => ?_⟩
  rcases hπ t with he | ⟨B, r, hprefix⟩
  · change ((fun x (e : ↥(N.cut (π.initial t) ∪ R)) =>
        p.trace I x e.val.signal.val) '' S).ncard ≤ _
    rw [he, Multigraph.cut_empty, empty_union]
    have h : ((fun x (e : R) => p.trace I x e.val.signal.val) '' S).ncard ≤
        2 ^ R.ncard := by
      simpa [Nat.card_fun, Nat.card_coe_set_eq, Nat.card_eq_fintype_card] using
        ncard_le_card ((fun x (e : R) => p.trace I x e.val.signal.val) '' S)
    apply h.trans
    apply Nat.pow_le_pow_right (by decide)
    lia
  let C := N.cut {v | key (c.blockOf v) < key B}
  let P := N.cut {v | c.blockOf v = B ∧ c.idx v < r}
  have hC : C ⊆ c.External := by
    intro e he h
    change c.blockOf (src e) = c.blockOf (tgt e) at h
    apply he
    change key (c.blockOf (src e)) < key B ↔ key (c.blockOf (tgt e)) < key B
    rw [h]
  have hwhole : ((fun x (e : C) => p.trace I x e.val.signal.val) '' S).ncard ≤ 2 ^ w := by
    have h := ncard_boundaryPatterns_le_oneSourceLabels p out I Acc c C hC S
    have hc : oneSourceLabels p out I Acc c C =
        (oneSourceHypergraph p out I Acc c).cut {B' | key B' < key B} :=
      oneSourceLabels_cut p out I Acc c {B' | key B' < key B}
    rw [hc] at h
    exact h.trans (Nat.pow_le_pow_right (by decide) (hw (key B)))
  have hpart : (P ∪ R).ncard ≤ d * Nat.log 2 (Nat.card (Vertex p out)) + d + R.ncard :=
    (ncard_union_le _ _).trans (Nat.add_le_add_right (c.ncard_cut_take_le B r) _)
  have hcover : N.frontier π t ∪ R ⊆ C ∪ (P ∪ R) := by
    rintro e (he | he)
    · change e ∈ N.cut (π.initial t) at he
      rw [hprefix] at he
      rcases N.cut_union_subset _ _ he with he | he
      · exact Or.inl he
      · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr he)
  calc
    _ ≤ ((fun x (e : C) => p.trace I x e.val.signal.val) '' S).ncard *
        2 ^ (P ∪ R).ncard := by
          simpa using Boundary.ncard_image_le_of_cover S (toFinite S)
            (N.frontier π t ∪ R) C (P ∪ R) hcover (fun x e => p.trace I x e.signal.val)
    _ ≤ 2 ^ w * 2 ^ (d * Nat.log 2 (Nat.card (Vertex p out)) + d + R.ncard) :=
      Nat.mul_le_mul hwhole (Nat.pow_le_pow_right (by decide) hpart)
    _ = _ := by rw [← pow_add]; congr 1; lia

end Frontier.Compiler
