/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Boundary.Hypergraph
public import Frontier.Boundary.Forest

/-!
# Closing one-bit relations before taking a boundary

Edges meeting at a marked vertex carry the same normalized value. Propagating
these relations through the whole graph, including edges outside the current
boundary, gives one value per connected component of the marked edge graph.
These components have connected occurrences in the original graph. Their
boundary capacity is therefore a hypergraph cut, and is submodular.

The counting theorem applies to any chosen set of inputs. In particular, the
code need only determine a transition on the inputs charged at that step.
-/

@[expose] public section

namespace Frontier

open Set

namespace Boundary

/-- Encode a chosen boundary by a structured part and an unstructured remainder.
The two parts may overlap; the remainder is charged by its raw alphabet size. -/
theorem ncard_image_le_of_cover {Ω E A : Type*} [Finite E] [Finite A]
    (S : Set Ω) (hS : S.Finite) (D C R : Set E) (hcover : D ⊆ C ∪ R)
    (f : Ω → E → A) :
    ((fun x (e : D) => f x e) '' S).ncard ≤
      ((fun x (e : C) => f x e) '' S).ncard * Nat.card A ^ R.ncard := by
  let code (x : Ω) := ((fun e : C => f x e), (fun e : R => f x e))
  have h := ncard_image_le_ncard_image_of_determines hS
    (fun x (e : D) => f x e) code ?_
  · refine h.trans ?_
    have hsub : code '' S ⊆ ((fun x (e : C) => f x e) '' S) ×ˢ (univ : Set (R → A)) := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, mem_univ _⟩
    simpa only [ncard_prod, ncard_univ, Nat.card_fun, Nat.card_coe_set_eq] using
      ncard_le_ncard hsub
  · intro x _ y _ hxy
    funext e
    rcases hcover e.property with he | he
    · exact congrFun (congrArg Prod.fst hxy) ⟨e, he⟩
    · exact congrFun (congrArg Prod.snd hxy) ⟨e, he⟩

/-- One representative value per label determines a pattern whenever equality
on one occurrence of a label implies equality on every other occurrence. -/
theorem ncard_image_le_labels {Ω E A Λ : Type*} [Finite E] [Finite A]
    (S : Set Ω) (hS : S.Finite) (D : Set E) (label : E → Λ) (f : Ω → E → A)
    (hdet : ∀ x ∈ S, ∀ y ∈ S, ∀ e e', label e = label e' →
      f x e' = f y e' → f x e = f y e) :
    ((fun x (e : D) => f x e) '' S).ncard ≤ Nat.card A ^ (label '' D).ncard := by
  classical
  let rep : (label '' D) → D := fun c => ⟨c.property.choose, c.property.choose_spec.1⟩
  have hrep (c : label '' D) : label (rep c) = c := c.property.choose_spec.2
  let code (x : Ω) (c : label '' D) := f x (rep c)
  have h := ncard_image_le_ncard_image_of_determines hS
    (fun x (e : D) => f x e) code ?_
  · refine h.trans ?_
    have := ncard_le_card (code '' S)
    simpa only [Nat.card_fun, Nat.card_coe_set_eq] using this
  · intro x hx y hy hxy
    funext e
    let c : label '' D := ⟨label e, e, e.property, rfl⟩
    exact hdet x hx y hy e (rep c) (hrep c).symm (congrFun hxy c)

end Boundary

namespace ForestBoundary

/-- Closing more equality relations never loses the savings certified by a
forest of local scopes. A local determining set must meet every global label. -/
theorem ncard_labels_le {V E Λ : Type*} [DecidableEq E]
    (J : V → Finset E)
    (hJ : Pairwise fun v w => ((J v : Set E) ∩ J w).Subsingleton)
    (hforest : (overlap J).IsAcyclic) (I : Finset V) (D : Finset E)
    (hsub : ∀ v ∈ I, J v ⊆ D) (label : E → Λ)
    (hlabel : ∀ v ∈ I, ∀ e ∈ J v, ∀ f ∈ J v, label e = label f) :
    (label '' (D : Set E)).ncard ≤ D.card - ∑ v ∈ I, ((J v).card - 1) := by
  classical
  obtain ⟨C, hCD, hcard, hdet, _⟩ := exists_code (A := Bool) J hJ hforest I D hsub
  have himage : label '' (D : Set E) = label '' (C : Set E) := by
    apply subset_antisymm ?_ (image_mono hCD)
    rintro _ ⟨e, he, rfl⟩
    by_contra hnone
    let f : E → Bool := fun e' => decide (label e' = label e)
    have hf : Compatible I J f := by
      intro v hv a ha b hb
      simp only [f, hlabel v hv a ha b hb]
    have hC : Set.EqOn f (fun _ => false) C := by
      intro e' he'
      have hne : label e' ≠ label e := fun h => hnone ⟨e', he', h⟩
      simp [f, hne]
    have := hdet f (fun _ => false) hf (fun _ _ _ _ _ _ => rfl) hC he
    simp [f] at this
  rw [himage]
  have hcount : (label '' (C : Set E)).ncard ≤ C.card := by
    simpa using (ncard_image_le C.finite_toSet (f := label))
  lia

end ForestBoundary

namespace Multigraph

variable {V E : Type*} (G : Multigraph V E) (U : Set V)

/-- Join two edges when they meet at a marked vertex. Connectivity is taken in
the whole graph, not just the current boundary. -/
def markedEdgeGraph : SimpleGraph E where
  Adj e f := e ≠ f ∧ ∃ v ∈ U, G.Incident v e ∧ G.Incident v f
  symm := ⟨by
    rintro e f ⟨hne, v, hv, he, hf⟩
    exact ⟨hne.symm, v, hv, hf, he⟩⟩
  loopless := ⟨by intro e h; exact h.1 rfl⟩

/-- The semantic label obtained by closing the marked incidence relations. -/
abbrev markedLabel : E → (G.markedEdgeGraph U).ConnectedComponent :=
  (G.markedEdgeGraph U).connectedComponentMk

theorem markedLabel_eq_of_incident {v : V} (hv : v ∈ U) {e f : E}
    (he : G.Incident v e) (hf : G.Incident v f) :
    G.markedLabel U e = G.markedLabel U f := by
  by_cases h : e = f
  · exact congrArg _ h
  · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
      ⟨h, v, hv, he, hf⟩

/-- A value constant on marked incidence scopes is constant on their closure. -/
theorem eq_of_markedLabel_eq {A : Type*} (f : E → A)
    (hf : ∀ v ∈ U, ∀ e, G.Incident v e → ∀ e', G.Incident v e' → f e = f e')
    {e e' : E} (h : G.markedLabel U e = G.markedLabel U e') : f e = f e' := by
  have hwalk := ((G.markedEdgeGraph U).reachable_iff_reflTransGen e e').mp
    (SimpleGraph.ConnectedComponent.exact h)
  clear h
  induction hwalk with
  | refl => rfl
  | @tail b c _ hbc ih =>
    obtain ⟨_, v, hv, hb, hc⟩ := hbc
    exact ih.trans (hf v hv b hb c hc)

private theorem incident_path {H : Multigraph V E} {e : E} {u v : V}
    (hu : H.Incident u e) (hv : H.Incident v e) :
    Relation.ReflTransGen H.Adj u v := by
  rcases hu with rfl | rfl <;> rcases hv with h | h
  · exact h ▸ .refl
  · exact .single ⟨e, Or.inl ⟨rfl, h⟩⟩
  · exact .single ⟨e, Or.inr ⟨h, rfl⟩⟩
  · exact h ▸ .refl

/-- Every closed label has connected occurrences in the original multigraph. -/
theorem markedLabel_connected (s : (G.markedEdgeGraph U).ConnectedComponent)
    {u v : V} (hu : u ∈ G.signalHypergraph (G.markedLabel U) s)
    (hv : v ∈ G.signalHypergraph (G.markedLabel U) s) :
    Relation.ReflTransGen (G.labelGraph (G.markedLabel U) s).Adj u v := by
  obtain ⟨e, he, hu⟩ := hu
  obtain ⟨f, hf, hv⟩ := hv
  have hwalk := ((G.markedEdgeGraph U).reachable_iff_reflTransGen e f).mp
    (SimpleGraph.ConnectedComponent.exact (he.trans hf.symm))
  have hpath : G.markedLabel U f = s ∧
      Relation.ReflTransGen (G.labelGraph (G.markedLabel U) s).Adj (G.src e) (G.src f) := by
    clear hf hv
    induction hwalk with
    | refl => exact ⟨he, .refl⟩
    | @tail b c _ hbc ih =>
      obtain ⟨_, w, hw, hb, hc⟩ := hbc
      have hc' : G.markedLabel U c = s :=
        (G.markedLabel_eq_of_incident U hw hc hb).trans ih.1
      refine ⟨hc', ih.2.trans ?_⟩
      exact (incident_path (H := G.labelGraph (G.markedLabel U) s)
        (e := ⟨b, ih.1⟩) (Or.inl rfl) hb).trans
        (incident_path (H := G.labelGraph (G.markedLabel U) s)
          (e := ⟨c, hc'⟩) hc (Or.inl rfl))
  exact (incident_path (H := G.labelGraph (G.markedLabel U) s)
    (e := ⟨e, he⟩) hu (Or.inl rfl)).trans
    (hpath.2.trans (incident_path (H := G.labelGraph (G.markedLabel U) s)
      (e := ⟨f, hf⟩) (Or.inl rfl) hv))

/-- Closing the relations first gives exactly a hypergraph boundary. -/
theorem image_markedLabel_cut (X : Set V) :
    G.markedLabel U '' G.cut X = (G.signalHypergraph (G.markedLabel U)).cut X :=
  G.image_cut_eq_hypergraph_cut _ (fun s _ hu _ hv => G.markedLabel_connected U s hu hv) X

/-- Unlike the boundary-local forest deficit, the globally closed capacity is
submodular, so a single patch ordering can minimize all thresholds. -/
theorem ncard_markedLabel_cut_submodular [Finite E] (X Y : Set V) :
    (G.markedLabel U '' G.cut (X ∩ Y)).ncard +
        (G.markedLabel U '' G.cut (X ∪ Y)).ncard ≤
      (G.markedLabel U '' G.cut X).ncard + (G.markedLabel U '' G.cut Y).ncard := by
  simp only [G.image_markedLabel_cut U]
  exact Hypergraph.ncard_cut_submodular _ X Y

/-- Equal normalized values on marked scopes give a code for an arbitrary
chosen edge set, including a whole charged transition. -/
theorem ncard_image_le_markedLabels {Ω A : Type*} [Finite E] [Finite A]
    (S : Set Ω) (hS : S.Finite) (D : Set E) (f : Ω → E → A)
    (hf : ∀ x ∈ S, ∀ v ∈ U, ∀ e, G.Incident v e →
      ∀ e', G.Incident v e' → f x e = f x e') :
    ((fun x (e : D) => f x e) '' S).ncard ≤ Nat.card A ^ (G.markedLabel U '' D).ncard := by
  apply Boundary.ncard_image_le_labels S hS D (G.markedLabel U) f
  intro x hx y hy e e' he hxy
  exact (G.eq_of_markedLabel_eq U (f x) (hf x hx) he).trans
    (hxy.trans (G.eq_of_markedLabel_eq U (f y) (hf y hy) he).symm)

end Multigraph

end Frontier
