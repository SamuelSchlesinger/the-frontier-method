/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Compiler.Source
public import Frontier.Boundary.Closure
public import Frontier.Layouts.Patch

/-!
# A global one-source boundary code

Delete constant ports and close the equal-or-complementary relations through
all one-source blocks before taking a boundary. One bit per resulting class
determines the whole chosen external pattern. This works for arbitrary
compressions, with constant signals, and on any chosen set of inputs.

The classes form a hypergraph of degree at most the compressed graph's degree.
Its cut capacity is submodular, so existing patch optimization and tie bounds
apply. No quantitative bound on its width in terms of the gate count is assumed
or proved here.
-/

@[expose] public section

namespace Frontier.Compiler

open Cslib.Circuits Set

variable {σ : Signature} {n s : ℕ} {O : Type*} [Finite O]
  (p : Program σ n s) (out : O → Wire n s)
  (I : Interpretation σ Bool) (Acc : O → Set Bool) {d : ℕ}
  (c : Multigraph.Compression (network p out I Acc).toMultigraph d)

/-- External ports whose value varies with the original input. -/
abbrev NonconstantExternal := {e : Edge p out // e ∈ c.External ∧
  ∃ x y, p.trace I x e.signal.val ≠ p.trace I y e.signal.val}

/-- The compression quotient with constant ports omitted. -/
noncomputable def nonconstantQuotient :
    Multigraph c.blocks (NonconstantExternal p out I Acc c) where
  src e := c.blockOf (src e.val)
  tgt e := c.blockOf (tgt e.val)

/-- Close all one-source relations in the quotient, including those outside
the boundary currently being encoded. -/
noncomputable abbrev oneSourceLabel := (nonconstantQuotient p out I Acc c).markedLabel
  {B | c.sourceLoad (inputVertices p out) B = 1}

/-- The closed labels needed by a chosen set of physical external edges. -/
def oneSourceLabels (D : Set (Edge p out)) :=
  oneSourceLabel p out I Acc c '' {e : NonconstantExternal p out I Acc c | e.val ∈ D}

/-- Each closed label is a connected hyperedge on the compressed blocks. -/
def oneSourceHypergraph := (nonconstantQuotient p out I Acc c).signalHypergraph
  (oneSourceLabel p out I Acc c)

/-- Normalizing against any fixed input makes all nonconstant ports in a
closed class equal. -/
theorem xor_eq_of_oneSourceLabel_eq (x y : Fin n → Bool)
    {e f : NonconstantExternal p out I Acc c}
    (h : oneSourceLabel p out I Acc c e = oneSourceLabel p out I Acc c f) :
    Bool.xor (p.trace I x e.val.signal.val) (p.trace I y e.val.signal.val) =
      Bool.xor (p.trace I x f.val.signal.val) (p.trace I y f.val.signal.val) := by
  apply (nonconstantQuotient p out I Acc c).eq_of_markedLabel_eq
    {B | c.sourceLoad (inputVertices p out) B = 1} _ ?_ h
  intro B hB a ha b hb
  exact oneSource_xor_of_nonconstant p out I Acc c B hB x y a.val b.val
    ha hb a.property.2 b.property.2

/-- The entire chosen boundary is encoded by one bit per nonconstant closed
label. Constants need no bits, and no finality or nonconstancy assumption is
imposed on the circuit or its compression. -/
theorem ncard_boundaryPatterns_le_oneSourceLabels (D : Set (Edge p out))
    (hD : D ⊆ c.External) (S : Set (Fin n → Bool)) :
    ((fun x (e : D) => p.trace I x e.val.signal.val) '' S).ncard ≤
      2 ^ (oneSourceLabels p out I Acc c D).ncard := by
  classical
  let D' : Set (NonconstantExternal p out I Acc c) := {e | e.val ∈ D}
  let pattern (x : Fin n → Bool) (e : D') := p.trace I x e.val.val.signal.val
  have hbound : (pattern '' S).ncard ≤ 2 ^ (oneSourceLabels p out I Acc c D).ncard := by
    have h := Boundary.ncard_image_le_labels S (toFinite S) D' (oneSourceLabel p out I Acc c)
      (fun x e => p.trace I x e.val.signal.val) ?_
    · simpa [oneSourceLabels, D', pattern] using h
    · intro x _ y _ e e' he hxy
      have h := xor_eq_of_oneSourceLabel_eq p out I Acc c x y he
      rw [hxy, Bool.xor_self] at h
      cases hx : p.trace I x e.val.signal.val <;>
        cases hy : p.trace I y e.val.signal.val <;> simp_all
  apply (ncard_image_le_ncard_image_of_determines (toFinite S)
    (fun x (e : D) => p.trace I x e.val.signal.val) pattern ?_).trans hbound
  intro x _ y _ hxy
  funext e
  by_cases he : ∃ u v, p.trace I u e.val.signal.val ≠ p.trace I v e.val.signal.val
  · exact congrFun hxy ⟨⟨e.val, hD e.property, he⟩, e.property⟩
  · by_contra h
    exact he ⟨x, y, h⟩

/-- The code may be used for a complete charged transition whenever the
chosen physical boundary determines that transition on its charged inputs. -/
theorem ncard_image_le_oneSourceLabels {M : Type*} (D : Set (Edge p out))
    (hD : D ⊆ c.External) (S : Set (Fin n → Bool)) (f : (Fin n → Bool) → M)
    (hdet : ∀ x ∈ S, ∀ y ∈ S,
      (∀ e ∈ D, p.trace I x e.signal.val = p.trace I y e.signal.val) → f x = f y) :
    (f '' S).ncard ≤ 2 ^ (oneSourceLabels p out I Acc c D).ncard := by
  apply (ncard_image_le_ncard_image_of_determines (toFinite S) f
    (fun x (e : D) => p.trace I x e.val.signal.val) ?_).trans
      (ncard_boundaryPatterns_le_oneSourceLabels p out I Acc c D hD S)
  intro x hx y hy hxy
  exact hdet x hx y hy fun e he => congrFun hxy ⟨e, he⟩

/-- The closed code cost on a block cut is exactly its hypergraph capacity. -/
theorem oneSourceLabels_cut (X : Set c.blocks) :
    oneSourceLabels p out I Acc c
        {e | ¬(c.blockOf (src e) ∈ X ↔ c.blockOf (tgt e) ∈ X)} =
      (oneSourceHypergraph p out I Acc c).cut X :=
  (nonconstantQuotient p out I Acc c).image_markedLabel_cut _ X

/-- Closing one-source relations gives a submodular capacity. -/
theorem oneSourceCapacity_submodular (X Y : Set c.blocks) :
    ((oneSourceHypergraph p out I Acc c).cut (X ∩ Y)).ncard +
        ((oneSourceHypergraph p out I Acc c).cut (X ∪ Y)).ncard ≤
      ((oneSourceHypergraph p out I Acc c).cut X).ncard +
        ((oneSourceHypergraph p out I Acc c).cut Y).ncard :=
  Hypergraph.ncard_cut_submodular _ X Y

/-- Closing and deleting ports cannot increase the degree. This supplies the
tie overhead required when converting threshold bounds into prefix bounds. -/
theorem oneSourceHypergraph_degree (B : c.blocks) :
    {a | B ∈ oneSourceHypergraph p out I Acc c a}.ncard ≤ d := by
  classical
  have heq : {a | B ∈ oneSourceHypergraph p out I Acc c a} =
      oneSourceLabel p out I Acc c '' (nonconstantQuotient p out I Acc c).edgesAt B := by
    ext a
    constructor <;> rintro ⟨e, h, h'⟩ <;> exact ⟨e, h', h⟩
  rw [heq]
  apply (ncard_image_le (toFinite _)).trans
  apply le_trans ?_ (c.multiQuotient_maxDegreeLE B)
  exact ncard_le_ncard_of_injOn
    (fun e : NonconstantExternal p out I Acc c => (⟨e.val, e.property.1⟩ : c.External))
    (fun _ he => he)
    (fun _ _ _ _ h => Subtype.ext (congrArg (fun e : c.External => e.val) h))

/-- One common key minimizes every threshold of the closed capacity inside
a patch; the outside keys remain fixed. -/
theorem exists_key_oneSource_minimum (patch : Finset c.blocks) (key : c.blocks → ℝ) :
    ∃ key' : c.blocks → ℝ, (∀ B, B ∉ patch → key' B = key B) ∧
      (∀ B, key' B ∈ Set.range key) ∧ ∀ t,
        PatchLayout.IsMinimum
          (fun X : Finset c.blocks => ((oneSourceHypergraph p out I Acc c).cut X).ncard)
          patch (Finset.univ.filter fun B => key B < t)
            (Finset.univ.filter fun B => key' B < t) :=
  Hypergraph.exists_key_patch_minimum _ patch key

end Frontier.Compiler
