/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Boundary.Code
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Boundary codes from a forest of equality constraints

Each scope requires its coordinates to agree. Distinct scopes share at most one
coordinate, and the graph of intersecting scopes is a forest. A scope of size `k`
then saves exactly `k - 1` coordinates: remove a leaf scope, retaining its one shared
coordinate (or any coordinate if it is disjoint from the others).

Translation gives the same capacity bound for consistent equality/complement
constraints on bits. This is a capacity certificate for a specified boundary; it
does not assert the existence of a layout with a uniformly positive saving.
-/

@[expose] public section

namespace Frontier.ForestBoundary

open Finset

variable {V E A : Type*} [DecidableEq E]

/-- Two distinct scopes are adjacent when they share a coordinate. -/
def overlap (J : V → Finset E) : SimpleGraph V where
  Adj v w := v ≠ w ∧ (J v ∩ J w).Nonempty
  symm := ⟨fun _ _ h => ⟨h.1.symm, by simpa only [Finset.inter_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Assignments satisfying all the equality constraints in the specified scopes. -/
def Compatible (I : Finset V) (J : V → Finset E) (f : E → A) : Prop :=
  ∀ v ∈ I, ∀ e ∈ J v, ∀ e' ∈ J v, f e = f e'

private theorem xor_apply (p : Bool → Bool) (hp : p false ≠ p true) (a b : Bool) :
    Bool.xor (p a) (p b) = Bool.xor a b := by
  cases a <;> cases b <;> cases hf : p false <;> cases ht : p true <;> simp_all

omit [DecidableEq E] in
/-- Nonconstant ports of a one-bit block are equal or complementary. Subtracting
any other realized pattern by XOR makes their differences constant on the scope. -/
theorem compatible_xor_of_one_bit (I : Finset V) (J : V → Finset E)
    (port : V → Bool → E → Bool)
    (hnonconst : ∀ v ∈ I, ∀ e ∈ J v, port v false e ≠ port v true e)
    (f g : E → Bool)
    (hf : ∀ v ∈ I, ∃ b, ∀ e ∈ J v, f e = port v b e)
    (hg : ∀ v ∈ I, ∃ b, ∀ e ∈ J v, g e = port v b e) :
    Compatible I J (fun e => Bool.xor (f e) (g e)) := by
  intro v hv e he e' he'
  obtain ⟨b, hb⟩ := hf v hv
  obtain ⟨c, hc⟩ := hg v hv
  change Bool.xor (f e) (g e) = Bool.xor (f e') (g e')
  rw [hb e he, hc e he, hb e' he', hc e' he']
  exact (xor_apply (fun a => port v a e) (hnonconst v hv e he) b c).trans
    (xor_apply (fun a => port v a e') (hnonconst v hv e' he') b c).symm

private theorem exists_leaf {W : Type*} [Finite W] [Nonempty W]
    (G : SimpleGraph W) (hG : G.IsAcyclic) :
    ∃ v, ∀ a b, G.Adj v a → G.Adj v b → a = b := by
  obtain ⟨v, w, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  have hs : ∀ a, G.Adj v a → a = p.snd := by
    intro a ha
    apply hG.eq_snd_of_adj_start hp ha
    have : ¬(p.cons ha.symm).IsPath := by
      intro h
      have := hmax _ _ _ h
      simp only [SimpleGraph.Walk.length_cons] at this
      lia
    grind [hp.cons]
  exact ⟨v, fun a b ha hb => (hs a ha).trans (hs b hb).symm⟩

/-- A leaf scope shares at most one coordinate with all the remaining scopes together. -/
theorem exists_leaf_scope [DecidableEq V] (J : V → Finset E)
    (hJ : Pairwise fun v w => ((J v : Set E) ∩ J w).Subsingleton)
    (hforest : (overlap J).IsAcyclic) (I : Finset V) (hI : I.Nonempty) :
    ∃ v ∈ I, (J v ∩ (I.erase v).biUnion J).card ≤ 1 := by
  have : Nonempty I := hI.to_subtype
  obtain ⟨v, hv⟩ := exists_leaf ((overlap J).induce (I : Set V)) (hforest.induce _)
  refine ⟨v, v.property, card_le_one.mpr ?_⟩
  intro e he e' he'
  obtain ⟨hev, he⟩ := mem_inter.mp he
  obtain ⟨he'v, he'⟩ := mem_inter.mp he'
  obtain ⟨w, hw, hew⟩ := mem_biUnion.mp he
  obtain ⟨w', hw', he'w⟩ := mem_biUnion.mp he'
  obtain ⟨hwv, hwI⟩ := mem_erase.mp hw
  obtain ⟨hw'v, hw'I⟩ := mem_erase.mp hw'
  have hww' : w = w' := congrArg Subtype.val (hv ⟨w, hwI⟩ ⟨w', hw'I⟩
    ⟨by simpa using hwv.symm, e, mem_inter.mpr ⟨hev, hew⟩⟩
    ⟨by simpa using hw'v.symm, e', mem_inter.mpr ⟨he'v, he'w⟩⟩)
  subst w'
  exact hJ hwv.symm ⟨hev, hew⟩ ⟨he'v, he'w⟩

/-- A coordinate code of the exact dimension, with both uniqueness and extension.
The ambient set `S` may contain coordinates outside every scope. -/
theorem exists_code (J : V → Finset E)
    (hJ : Pairwise fun v w => ((J v : Set E) ∩ J w).Subsingleton)
    (hforest : (overlap J).IsAcyclic) (I : Finset V) (S : Finset E)
    (hsub : ∀ v ∈ I, J v ⊆ S) :
    ∃ C ⊆ S, C.card + ∑ v ∈ I, ((J v).card - 1) = S.card ∧
      (∀ f g : E → A, Compatible I J f → Compatible I J g →
        Set.EqOn f g C → Set.EqOn f g S) ∧
      (∀ f : E → A, ∃ g : E → A, Compatible I J g ∧ Set.EqOn g f C) := by
  classical
  induction I using Finset.strongInductionOn generalizing S with
  | _ I ih =>
    rcases I.eq_empty_or_nonempty with rfl | hI
    · exact ⟨S, Finset.Subset.rfl, by simp, fun _ _ _ _ h => h,
        fun f => ⟨f, by simp [Compatible], fun _ _ => rfl⟩⟩
    obtain ⟨v, hv, hleaf⟩ := exists_leaf_scope J hJ hforest I hI
    have hsmall : I.erase v ⊂ I := erase_ssubset hv
    by_cases hne : (J v).Nonempty
    · have hp : ∃ p ∈ J v, J v ∩ (I.erase v).biUnion J ⊆ {p} := by
        rcases (J v ∩ (I.erase v).biUnion J).eq_empty_or_nonempty with hempty | hshared
        · obtain ⟨p, hp⟩ := hne
          exact ⟨p, hp, by simp [hempty]⟩
        · obtain ⟨p, hp⟩ := hshared
          refine ⟨p, (mem_inter.mp hp).1, fun e he => ?_⟩
          exact mem_singleton.mpr (card_le_one.mp hleaf e he p hp)
      obtain ⟨p, hp, hshared⟩ := hp
      let D := (J v).erase p
      have hD : D ⊆ S := fun e he => hsub v hv (mem_erase.mp he).2
      have hother : ∀ w ∈ I.erase v, J w ⊆ S \ D := by
        intro w hw e he
        refine mem_sdiff.mpr ⟨hsub w (mem_of_mem_erase hw) he, ?_⟩
        intro heD
        have hep := hshared (mem_inter.mpr
          ⟨(mem_erase.mp heD).2, mem_biUnion.mpr ⟨w, hw, he⟩⟩)
        exact (mem_erase.mp heD).1 (mem_singleton.mp hep)
      have hpS : p ∈ S \ D := mem_sdiff.mpr ⟨hsub v hv hp, by simp [D]⟩
      obtain ⟨C, hC, hcard, hinj, hext⟩ := ih (I.erase v) hsmall (S \ D) hother
      refine ⟨C, hC.trans sdiff_subset, ?_, ?_, ?_⟩
      · have hsum := sum_erase_add I (fun w => (J w).card - 1) hv
        have hdc : D.card = (J v).card - 1 := card_erase_of_mem hp
        have hsc := card_sdiff_add_card_eq_card hD
        lia
      · intro f g hf hg hfg e he
        have heq := hinj f g
          (fun w hw => hf w (mem_of_mem_erase hw))
          (fun w hw => hg w (mem_of_mem_erase hw)) hfg
        by_cases heD : e ∈ D
        · exact (hf v hv e (mem_erase.mp heD).2 p hp).trans
            ((heq hpS).trans (hg v hv p hp e (mem_erase.mp heD).2))
        · exact heq (mem_sdiff.mpr ⟨he, heD⟩)
      · intro f
        obtain ⟨g, hg, hgf⟩ := hext f
        let g' : E → A := fun e => if e ∈ D then g p else g e
        have hsame : Set.EqOn g' g (↑(S \ D) : Set E) := by
          intro e he
          simp [g', (mem_sdiff.mp he).2]
        refine ⟨g', ?_, fun e he => (hsame (hC he)).trans (hgf he)⟩
        intro w hw e he e' he'
        by_cases hwv : w = v
        · subst w
          have hval : ∀ a ∈ J v, g' a = g p := by
            intro a ha
            by_cases hap : a = p
            · simp [g', D, hap]
            · simp [g', D, ha, hap]
          exact (hval e he).trans (hval e' he').symm
        · have hw' := mem_erase.mpr ⟨hwv, hw⟩
          exact (hsame (hother w hw' he)).trans
            ((hg w hw' e he e' he').trans (hsame (hother w hw' he')).symm)
    · have hempty : J v = ∅ := not_nonempty_iff_eq_empty.mp hne
      obtain ⟨C, hC, hcard, hinj, hext⟩ := ih (I.erase v) hsmall S
        (fun w hw => hsub w (mem_of_mem_erase hw))
      refine ⟨C, hC, ?_, ?_, ?_⟩
      · have hsum := sum_erase_add I (fun w => (J w).card - 1) hv
        simp only [hempty, card_empty, Nat.zero_sub, add_zero] at hsum
        rwa [hsum] at hcard
      · exact fun f g hf hg => hinj f g
          (fun w hw => hf w (mem_of_mem_erase hw))
          (fun w hw => hg w (mem_of_mem_erase hw))
      · intro f
        obtain ⟨g, hg, hgf⟩ := hext f
        refine ⟨g, ?_, hgf⟩
        intro w hw e he
        by_cases hwv : w = v
        · simp [hwv, hempty] at he
        · exact hg w (mem_erase.mpr ⟨hwv, hw⟩) e he

section Capacity

variable [Fintype E] (J : V → Finset E)
  (hJ : Pairwise fun v w => ((J v : Set E) ∩ J w).Subsingleton)
  (hforest : (overlap J).IsAcyclic) (I : Finset V)

include hJ hforest

/-- Restriction to the retained coordinates is an exact code for compatible assignments. -/
theorem exists_bijective_restrict [Nonempty A] :
    ∃ C : Finset E, C.card + ∑ v ∈ I, ((J v).card - 1) = Fintype.card E ∧
      Function.Bijective (fun f : {f : E → A // Compatible I J f} =>
        fun e : C => f.val e) := by
  classical
  obtain ⟨C, _, hc, hinj, hext⟩ := exists_code (A := A) J hJ hforest I univ
    (fun _ _ => subset_univ _)
  refine ⟨C, by simpa using hc, ?_, ?_⟩
  · intro f g hfg
    apply Subtype.ext
    funext e
    exact hinj f g f.property g.property
      (fun a ha => congrFun hfg ⟨a, ha⟩) (mem_univ e)
  · intro f
    let f' : E → A := fun e => if he : e ∈ C then f ⟨e, he⟩ else Classical.choice ‹Nonempty A›
    obtain ⟨g, hg, hgf⟩ := hext f'
    refine ⟨⟨g, hg⟩, funext fun e => ?_⟩
    simpa [f', e.property] using hgf e.property

/-- The exact number of assignments satisfying a forest of equality scopes. -/
theorem ncard_compatible [Finite A] [Nonempty A] :
    {f : E → A | Compatible I J f}.ncard =
      Nat.card A ^ (Fintype.card E - ∑ v ∈ I, ((J v).card - 1)) := by
  obtain ⟨C, hc, hbij⟩ := exists_bijective_restrict (A := A) J hJ hforest I
  rw [← Nat.card_coe_set_eq]
  change Nat.card {f : E → A // Compatible I J f} = _
  rw [Nat.card_congr (Equiv.ofBijective _ hbij), Nat.card_fun,
    Nat.card_eq_fintype_card (α := C), Fintype.card_coe]
  congr 1
  lia

/-- Complementing fixed coordinates preserves the bound for Boolean patterns. -/
theorem ncard_le_of_compatible_xor (R : Set (E → Bool)) (base : E → Bool)
    (hR : ∀ f ∈ R, Compatible I J (fun e => Bool.xor (f e) (base e))) :
    R.ncard ≤ 2 ^ (Fintype.card E - ∑ v ∈ I, ((J v).card - 1)) := by
  let flip : (E → Bool) → (E → Bool) := fun f e => Bool.xor (f e) (base e)
  have hinj : Function.Injective flip := by
    intro f g h
    funext e
    have he := congrFun h e
    cases hb : base e <;> simpa [flip, hb] using he
  calc
    R.ncard = (flip '' R).ncard := (Set.ncard_image_of_injective R hinj).symm
    _ ≤ {f : E → Bool | Compatible I J f}.ncard :=
      Set.ncard_le_ncard (by rintro _ ⟨f, hf, rfl⟩; exact hR f hf)
    _ = _ := by simpa using ncard_compatible (A := Bool) J hJ hforest I

variable {F : Type*} [Field F]

/-- The homogeneous solution space of the scope equalities. -/
def solutionSpace : Submodule F (E → F) where
  carrier := {f | Compatible I J f}
  zero_mem' := by intro v hv e he e' he'; rfl
  add_mem' := by
    intro f g hf hg v hv e he e' he'
    exact congrArg₂ (· + ·) (hf v hv e he e' he') (hg v hv e he e' he')
  smul_mem' := by
    intro a f hf v hv e he e' he'
    exact congrArg (a * ·) (hf v hv e he e' he')

/-- The codimension is the sum of the local deficits, with no overlap correction. -/
theorem finrank_solutionSpace_add :
    Module.finrank F (solutionSpace (F := F) J I) +
      ∑ v ∈ I, ((J v).card - 1) = Fintype.card E := by
  obtain ⟨C, hc, hbij⟩ := exists_bijective_restrict (A := F) J hJ hforest I
  let R : solutionSpace (F := F) J I →ₗ[F] (C → F) :=
    { toFun := fun f e => f.val e
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hdim := (LinearEquiv.ofBijective R hbij).finrank_eq
  rw [Module.finrank_pi, Fintype.card_coe] at hdim
  lia

/-- All pairwise differences within each scope; redundant rows do not affect the rank. -/
def differences : (E → F) →ₗ[F] (∀ v : I, J v.val → J v.val → F) where
  toFun f _ e e' := f e - f e'
  map_add' := by intro f g; ext; simp; abel
  map_smul' := by intro a f; ext; simp [mul_sub]

omit hJ hforest [DecidableEq E] [Fintype E] in
theorem ker_differences :
    LinearMap.ker (differences (F := F) J I) = solutionSpace J I := by
  ext f
  change (fun (v : I) (e e' : J v.val) => f e - f e') = 0 ↔ Compatible I J f
  simp only [funext_iff, Pi.zero_apply, sub_eq_zero, Subtype.forall, Compatible]

omit [Fintype E] in
/-- The equality equations have exactly the rank claimed by leaf peeling. -/
theorem finrank_differences [Finite E] :
    Module.finrank F (LinearMap.range (differences (F := F) J I)) =
      ∑ v ∈ I, ((J v).card - 1) := by
  let _ := Fintype.ofFinite E
  have h := (differences (F := F) J I).finrank_range_add_finrank_ker
  rw [ker_differences, Module.finrank_pi] at h
  have hc := finrank_solutionSpace_add (F := F) J hJ hforest I
  lia

/-- A fixed translation gives the same capacity bound. In characteristic two this
covers consistent equality/complement constraints on boundary bits. -/
theorem ncard_le_of_compatible_sub [Finite F] (R : Set (E → F)) (base : E → F)
    (hR : ∀ f ∈ R, Compatible I J (f - base)) :
    R.ncard ≤ Nat.card F ^ (Fintype.card E - ∑ v ∈ I, ((J v).card - 1)) := by
  calc
    R.ncard = ((fun f => f - base) '' R).ncard :=
      (Set.ncard_image_of_injective R fun _ _ h => by simpa using h).symm
    _ ≤ {f : E → F | Compatible I J f}.ncard :=
      Set.ncard_le_ncard (by rintro _ ⟨f, hf, rfl⟩; exact hR f hf)
    _ = _ := ncard_compatible J hJ hforest I

end Capacity

section Graph

variable {W : Type*} [DecidableEq W]

/-- The coordinates incident to a marked vertex, restricted to a chosen edge boundary.
The boundary may be any set of edges, in particular a cut. -/
def incidentScopes (D : Finset (Sym2 W)) (U : Finset W) (v : U) : Finset D :=
  univ.filter fun e => v.val ∈ e.val

theorem incidentScopes_pairwise (D : Finset (Sym2 W)) (U : Finset W) :
    Pairwise fun v w : U =>
      ((incidentScopes D U v : Set D) ∩ incidentScopes D U w).Subsingleton := by
  intro v w hvw e he e' he'
  apply Subtype.ext
  exact Sym2.eq_of_ne_mem (Subtype.val_injective.ne hvw)
    (mem_filter.mp he.1).2 (mem_filter.mp he.2).2
    (mem_filter.mp he'.1).2 (mem_filter.mp he'.2).2

/-- Intersecting stars are adjacent in the marked induced graph. -/
theorem overlap_incidentScopes_le (G : SimpleGraph W) (D : Finset (Sym2 W)) (U : Finset W)
    (hD : (D : Set (Sym2 W)) ⊆ G.edgeSet) :
    overlap (incidentScopes D U) ≤ G.induce (U : Set W) := by
  intro v w h
  obtain ⟨e, he⟩ := h.2
  have hends : e.val = s(v.val, w.val) :=
    (Sym2.mem_and_mem_iff (Subtype.val_injective.ne h.1)).mp
      ⟨(mem_filter.mp (mem_inter.mp he).1).2, (mem_filter.mp (mem_inter.mp he).2).2⟩
  exact G.mem_edgeSet.mp (hends ▸ hD e.property)

/-- A forest of marked vertices gives a forest of boundary scopes. -/
theorem incidentScopes_acyclic (G : SimpleGraph W) (D : Finset (Sym2 W)) (U : Finset W)
    (hD : (D : Set (Sym2 W)) ⊆ G.edgeSet) (hU : (G.induce (U : Set W)).IsAcyclic) :
    (overlap (incidentScopes D U)).IsAcyclic :=
  hU.anti (overlap_incidentScopes_le G D U hD)

/-- On any boundary, the rank saved by a forest of marked stars is exactly
`∑ v, max(k_v - 1, 0)`, where `k_v` counts the boundary edges incident to `v`. -/
theorem finrank_incident_differences {F : Type*} [Field F]
    (G : SimpleGraph W) (D : Finset (Sym2 W)) (U : Finset W)
    (hD : (D : Set (Sym2 W)) ⊆ G.edgeSet) (hU : (G.induce (U : Set W)).IsAcyclic) :
    Module.finrank F (LinearMap.range (differences (F := F) (incidentScopes D U) univ)) =
      ∑ v : U, ((incidentScopes D U v).card - 1) :=
  finrank_differences _ (incidentScopes_pairwise D U) (incidentScopes_acyclic G D U hD hU) _

/-- The semantic boundary capacity certificate. After one fixed translation,
every realized pattern must be constant on each marked star. -/
theorem ncard_le_incident {F : Type*} [Field F] [Finite F]
    (G : SimpleGraph W) (D : Finset (Sym2 W)) (U : Finset W)
    (hD : (D : Set (Sym2 W)) ⊆ G.edgeSet) (hU : (G.induce (U : Set W)).IsAcyclic)
    (R : Set (D → F)) (base : D → F)
    (hR : ∀ f ∈ R, Compatible univ (incidentScopes D U) (f - base)) :
    R.ncard ≤ Nat.card F ^ (D.card - ∑ v : U, ((incidentScopes D U v).card - 1)) := by
  simpa only [Fintype.card_coe] using ncard_le_of_compatible_sub (incidentScopes D U)
    (incidentScopes_pairwise D U) (incidentScopes_acyclic G D U hD hU) univ R base hR

/-- The binary capacity bound `|R| ≤ 2^(|D| - ∑ v, (k_v - 1))` for consistent
equality/complement constraints on the boundary edges. -/
theorem ncard_le_incident_xor
    (G : SimpleGraph W) (D : Finset (Sym2 W)) (U : Finset W)
    (hD : (D : Set (Sym2 W)) ⊆ G.edgeSet) (hU : (G.induce (U : Set W)).IsAcyclic)
    (R : Set (D → Bool)) (base : D → Bool)
    (hR : ∀ f ∈ R,
      Compatible univ (incidentScopes D U) (fun e => Bool.xor (f e) (base e))) :
    R.ncard ≤ 2 ^ (D.card - ∑ v : U, ((incidentScopes D U v).card - 1)) := by
  simpa only [Fintype.card_coe] using ncard_le_of_compatible_xor (incidentScopes D U)
    (incidentScopes_pairwise D U) (incidentScopes_acyclic G D U hD hU) univ R base hR

end Graph

end Frontier.ForestBoundary

namespace Frontier.Sweep

open ForestBoundary

variable {ι A M W : Type*} [Finite ι] [Finite A] [DecidableEq W]
  {S : Set (ι → A)} (P : Sweep S M)

/-- Forest savings may be used as transition capacity, provided the edge pattern
determines both adjacent messages and all newly read inputs. -/
theorem transitionCount_le_forest_codes
    (G : SimpleGraph W) (D : ℕ → Finset (Sym2 W)) (U : ℕ → Finset W)
    (hD : ∀ t < P.length, (D t : Set (Sym2 W)) ⊆ G.edgeSet)
    (hU : ∀ t < P.length, (G.induce (U t : Set W)).IsAcyclic)
    (code : ∀ t, (ι → A) → (D t → Bool)) (base : ∀ t, D t → Bool)
    (hcomp : ∀ t < P.length, ∀ x ∈ S,
      Compatible Finset.univ (incidentScopes (D t) (U t))
        (fun e => Bool.xor (code t x e) (base t e)))
    (hdet : ∀ t < P.length, ∀ x ∈ S, ∀ y ∈ S,
      code t x = code t y → P.transition t x = P.transition t y) :
    P.transitionCount ≤ ∑ t ∈ Finset.range P.length,
      2 ^ ((D t).card - ∑ v : U t, ((incidentScopes (D t) (U t) v).card - 1)) := by
  refine (P.transitionCount_le_codes code (fun t => code t '' S)
    (fun _ _ => Set.toFinite _) (fun _ _ x hx => ⟨x, hx, rfl⟩) hdet).trans ?_
  refine Finset.sum_le_sum fun t ht => ?_
  have ht := Finset.mem_range.mp ht
  exact ncard_le_incident_xor G (D t) (U t) (hD t ht) (hU t ht) (code t '' S) (base t)
    (by rintro _ ⟨x, hx, rfl⟩; exact hcomp t ht x hx)

end Frontier.Sweep
