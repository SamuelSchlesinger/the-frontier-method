/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Frontier.Boundary.Closure
import Mathlib.Tactic.FinCases

/-!
# Why global closure matters

In K₄ mark vertices 0 and 1. They induce a single edge, hence a forest. The
boundary-local exponent is not submodular: the cuts A={0,2} and B={1,2} cost
two each, while their intersection and union cost three each.

Closing the marked relations globally merges edges 01,02,03,12,13. Edge 23
is a separate class. The cut {2} therefore costs only two bits, saving a bit
that the local forest formula misses. The missing relation passes through
edge 01, which is not on that cut.
-/

namespace Frontier.Examples.Closure

open Finset

def graph : Multigraph (Fin 4) (Fin 6) where
  src := ![0, 0, 0, 1, 1, 2]
  tgt := ![1, 2, 3, 2, 3, 3]

def marked : Finset (Fin 4) := {0, 1}

def cut (X : Finset (Fin 4)) : Finset (Fin 6) :=
  univ.filter fun e => ¬(graph.src e ∈ X ↔ graph.tgt e ∈ X)

def localCapacity (X : Finset (Fin 4)) : ℕ :=
  (cut X).card - ∑ v ∈ marked,
    (((cut X).filter fun e => graph.src e = v ∨ graph.tgt e = v).card - 1)

theorem localCapacity_values :
    localCapacity ({0, 2} ∩ {1, 2}) = 3 ∧
    localCapacity ({0, 2} ∪ {1, 2}) = 3 ∧
    localCapacity {0, 2} = 2 ∧ localCapacity {1, 2} = 2 := by decide

theorem localCapacity_not_submodular :
    ¬∀ A B, localCapacity (A ∩ B) + localCapacity (A ∪ B) ≤
      localCapacity A + localCapacity B := by
  intro h
  have := h {0, 2} {1, 2}
  obtain ⟨hi, hu, ha, hb⟩ := localCapacity_values
  lia

/-- The marked induced graph has only two vertices, so is a forest. -/
theorem marked_acyclic : ((⊤ : SimpleGraph (Fin 4)).induce (marked : Set (Fin 4))).IsAcyclic := by
  apply SimpleGraph.IsAcyclic.of_card_le_two
  simp [ENat.card_eq_coe_fintype_card, marked]

private theorem label_eq_zero (e : Fin 6) (he : e ≠ 5) :
    graph.markedLabel (marked : Set (Fin 4)) e =
      graph.markedLabel (marked : Set (Fin 4)) 0 := by
  fin_cases e
  · rfl
  · exact graph.markedLabel_eq_of_incident _ (v := 0) (by decide)
      (by simp [Multigraph.Incident, graph]) (by simp [Multigraph.Incident, graph])
  · exact graph.markedLabel_eq_of_incident _ (v := 0) (by decide)
      (by simp [Multigraph.Incident, graph]) (by simp [Multigraph.Incident, graph])
  · exact graph.markedLabel_eq_of_incident _ (v := 1) (by decide)
      (by simp [Multigraph.Incident, graph]) (by simp [Multigraph.Incident, graph])
  · exact graph.markedLabel_eq_of_incident _ (v := 1) (by decide)
      (by simp [Multigraph.Incident, graph]) (by simp [Multigraph.Incident, graph])
  · exact (he rfl).elim

private theorem label_zero_ne_five :
    graph.markedLabel (marked : Set (Fin 4)) 0 ≠
      graph.markedLabel (marked : Set (Fin 4)) 5 := by
  intro h
  have hconst : ∀ v ∈ (marked : Set (Fin 4)), ∀ e, graph.Incident v e →
      ∀ f, graph.Incident v f → (decide (e = 5) : Bool) = decide (f = 5) := by
    unfold Multigraph.Incident
    decide
  have := graph.eq_of_markedLabel_eq _ (fun e => decide (e = 5)) hconst h
  contradiction

/-- Closure saves a full bit at this cut, through an edge outside the cut. -/
theorem closedCapacity_strict :
    (graph.markedLabel (marked : Set (Fin 4)) '' graph.cut {2}).ncard = 2 ∧
      localCapacity {2} = 3 := by
  constructor
  · have heq : graph.markedLabel (marked : Set (Fin 4)) '' graph.cut {2} =
        {graph.markedLabel (marked : Set (Fin 4)) 0,
          graph.markedLabel (marked : Set (Fin 4)) 5} := by
      ext a
      constructor
      · rintro ⟨e, he, rfl⟩
        by_cases h : e = 5
        · simp [h]
        · simp [label_eq_zero e h]
      · rintro (rfl | rfl)
        · exact ⟨1, by simp [Multigraph.cut, graph], label_eq_zero 1 (by decide)⟩
        · exact ⟨5, by simp [Multigraph.cut, graph], rfl⟩
    rw [heq, Set.ncard_pair label_zero_ne_five]
  · decide

end Frontier.Examples.Closure
