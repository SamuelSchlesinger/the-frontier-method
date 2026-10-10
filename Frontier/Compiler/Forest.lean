/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Compiler.Source

/-!
# Forest capacity of a compressed circuit

The one-source forest and one-bit block semantics supplied by the compiler give
an actual bound on realized Boolean boundary patterns. For any external edge set
`D`, subtract `max(k_B - 1, 0)` for every one-source block, where `k_B` counts its
incident edges in `D`. The bound holds for any input set, including inputs charged
at a specified transition. The circuit signals must be nonconstant; a separate
normalization is needed before applying this version to a circuit with constants.

No bound on the maximum of this exponent over a layout is asserted here.
-/

@[expose] public section

namespace Frontier.Multigraph.Compression

open Finset

variable {V E : Type*} {G : Multigraph V E} {d : ℕ} (c : Compression G d)

/-- The chosen external edges incident to a marked block. -/
noncomputable def boundaryScopes (D : Finset E) (U : Set c.blocks) (B : U) : Finset D := by
  classical
  exact univ.filter fun e => B.val ∈ c.ends e.val

/-- A simple final quotient makes distinct boundary scopes overlap in at most one edge. -/
theorem boundaryScopes_pairwise [Finite E] (hc : c.Final) (D : Finset E)
    (hD : ∀ e ∈ D, e ∈ c.External) (U : Set c.blocks) :
    Pairwise fun v w : U =>
      ((c.boundaryScopes D U v : Set D) ∩ c.boundaryScopes D U w).Subsingleton := by
  classical
  intro v w hvw e he e' he'
  apply Subtype.ext
  apply c.injOn_ends hc (hD _ e.property) (hD _ e'.property)
  exact Sym2.eq_of_ne_mem (Subtype.val_injective.ne hvw)
    (mem_filter.mp he.1).2 (mem_filter.mp he.2).2
    (mem_filter.mp he'.1).2 (mem_filter.mp he'.2).2

open Classical in
/-- Intersecting boundary scopes are adjacent in the induced quotient. -/
theorem overlap_boundaryScopes_le (D : Finset E) (U : Set c.blocks) :
    ForestBoundary.overlap (c.boundaryScopes D U) ≤ c.quotient.induce U := by
  classical
  intro v w h
  obtain ⟨e, he⟩ := h.2
  have hends : c.ends e.val = s(v.val, w.val) :=
    (Sym2.mem_and_mem_iff (Subtype.val_injective.ne h.1)).mp
      ⟨(mem_filter.mp (mem_inter.mp he).1).2, (mem_filter.mp (mem_inter.mp he).2).2⟩
  exact ⟨Subtype.val_injective.ne h.1, e.val, hends⟩

end Frontier.Multigraph.Compression

namespace Frontier.Compiler

open Cslib.Circuits Finset

variable {σ : Signature} {n s : ℕ} {O : Type*} [Finite O]
  (p : Program σ n s) (out : O → Wire n s)
  (I : Interpretation σ Bool) (Acc : O → Set Bool) {d : ℕ}
  (c : Multigraph.Compression (network p out I Acc).toMultigraph d)

open Classical in
/-- The compiler's one-source blocks give an exact forest deficit in the exponent
of the realized pattern bound. This counts only the chosen input set `S`. -/
theorem ncard_boundaryPatterns_le (hc : c.Final)
    (hnonconst : ∀ e : Edge p out, ∃ x y,
      p.trace I x e.signal.val ≠ p.trace I y e.signal.val)
    (D : Finset (Edge p out)) (hD : ∀ e ∈ D, e ∈ c.External) (S : Set (Fin n → Bool)) :
    ((fun x (e : D) => p.trace I x e.val.signal.val) '' S).ncard ≤
      2 ^ (D.card - ∑ B : {B // c.sourceLoad (inputVertices p out) B = 1},
        ((c.boundaryScopes D {B | c.sourceLoad (inputVertices p out) B = 1} B).card - 1)) := by
  classical
  let U : Set c.blocks := {B | c.sourceLoad (inputVertices p out) B = 1}
  have hforest : (ForestBoundary.overlap (c.boundaryScopes D U)).IsAcyclic :=
    (oneSource_acyclic p out I Acc c (arity_ne_zero_of_nonconstant p out I hnonconst)).anti
      (c.overlap_boundaryScopes_le D U)
  have h := ForestBoundary.ncard_le_of_compatible_xor (c.boundaryScopes D U)
    (c.boundaryScopes_pairwise hc D hD U) hforest univ
    ((fun x (e : D) => p.trace I x e.val.signal.val) '' S)
    (fun e => p.trace I (fun _ => false) e.val.signal.val) ?_
  · simp only [Fintype.card_coe] at h
    convert h using 1
    congr 2
  · rintro _ ⟨x, _, rfl⟩ B _ e he e' he'
    have hb : c.blockOf (src e.val) = B.val ∨ c.blockOf (tgt e.val) = B.val := by
      simpa [Multigraph.Compression.boundaryScopes, Multigraph.Compression.ends, network,
        eq_comm] using he
    have hb' : c.blockOf (src e'.val) = B.val ∨ c.blockOf (tgt e'.val) = B.val := by
      simpa [Multigraph.Compression.boundaryScopes, Multigraph.Compression.ends, network,
        eq_comm] using he'
    exact oneSource_xor p out I Acc c B.val B.property (fun e _ => hnonconst e)
      x (fun _ => false) e.val e'.val hb hb'

open Classical in
/-- Apply the concrete circuit certificate to any information determined by the
boundary, in particular to a complete transition on its charged input set. -/
theorem ncard_image_le_oneSource {M : Type*} (hc : c.Final)
    (hnonconst : ∀ e : Edge p out, ∃ x y,
      p.trace I x e.signal.val ≠ p.trace I y e.signal.val)
    (D : Finset (Edge p out)) (hD : ∀ e ∈ D, e ∈ c.External)
    (S : Set (Fin n → Bool)) (f : (Fin n → Bool) → M)
    (hdet : ∀ x ∈ S, ∀ y ∈ S,
      (∀ e ∈ D, p.trace I x e.signal.val = p.trace I y e.signal.val) → f x = f y) :
    (f '' S).ncard ≤
      2 ^ (D.card - ∑ B : {B // c.sourceLoad (inputVertices p out) B = 1},
        ((c.boundaryScopes D {B | c.sourceLoad (inputVertices p out) B = 1} B).card - 1)) := by
  apply (Set.ncard_image_le_ncard_image_of_determines (Set.toFinite S) f
    (fun x (e : D) => p.trace I x e.val.signal.val) ?_).trans
      (ncard_boundaryPatterns_le p out I Acc c hc hnonconst D hD S)
  intro x hx y hy hxy
  exact hdet x hx y hy fun e he => congrFun hxy ⟨e, he⟩

end Frontier.Compiler
