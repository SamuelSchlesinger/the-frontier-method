/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Cuts of simple graphs

`SimpleGraph.cutFinset S` is the set of edges of a finite simple graph with exactly one endpoint
in `S`. An upstreaming candidate.
-/

@[expose] public section

namespace SimpleGraph

variable {W : Type*} (H : SimpleGraph W) [Fintype H.edgeSet]

open Classical in
/-- The edges of a simple graph with exactly one endpoint in `S`. -/
noncomputable def cutFinset (S : Finset W) : Finset (Sym2 W) :=
  H.edgeFinset.filter fun e => ∃ a b, e = s(a, b) ∧ a ∈ S ∧ b ∉ S

variable {H}

theorem mem_cutFinset {S : Finset W} {e : Sym2 W} :
    e ∈ H.cutFinset S ↔ e ∈ H.edgeSet ∧ ∃ a b, e = s(a, b) ∧ a ∈ S ∧ b ∉ S := by
  simp [cutFinset, mem_edgeFinset]

/-- An edge crosses `S` exactly when it is an edge with one endpoint on each side. -/
theorem mem_cutFinset_mk {S : Finset W} {a b : W} :
    s(a, b) ∈ H.cutFinset S ↔ H.Adj a b ∧ ((a ∈ S ∧ b ∉ S) ∨ (b ∈ S ∧ a ∉ S)) := by
  rw [mem_cutFinset, mem_edgeSet]
  constructor
  · rintro ⟨adj, x, y, hxy, hx, hy⟩
    refine ⟨adj, ?_⟩
    rcases Sym2.eq_iff.mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hx, hy⟩
    · exact Or.inr ⟨hx, hy⟩
  · rintro ⟨adj, ⟨ha, hb⟩ | ⟨hb, ha⟩⟩
    · exact ⟨adj, a, b, rfl, ha, hb⟩
    · exact ⟨adj, b, a, Sym2.eq_swap, hb, ha⟩

theorem cutFinset_subset_edgeFinset (S : Finset W) : H.cutFinset S ⊆ H.edgeFinset :=
  fun _ he => mem_edgeFinset.mpr (mem_cutFinset.mp he).1

/-- A graph with at most one vertex has no crossing edges. -/
theorem cutFinset_eq_empty_of_subsingleton [Subsingleton W] (S : Finset W) :
    H.cutFinset S = ∅ := by
  ext e
  simp only [Finset.notMem_empty, iff_false]
  intro he
  obtain ⟨_, a, b, _, ha, hb⟩ := mem_cutFinset.mp he
  exact hb (Subsingleton.elim a b ▸ ha)

end SimpleGraph
