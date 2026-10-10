/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Boundary.Hypergraph
public import Frontier.Boundary.Observation
import Mathlib.Data.Finset.Max

/-!
# Optimizing a patch at every threshold

For a submodular cut cost, minimum cuts with nested boundary conditions can be
chosen nested. The proof is the usual uncrossing argument: intersection is
feasible for the earlier boundary and union for the later one. Choosing the
largest minimizer gives a monotone map on cuts.

This is an instance of monotone submodular optimization; see Donald M. Topkis,
*Minimizing a Submodular Function on a Lattice*, Operations Research 26(2), 1978,
https://doi.org/10.1287/opre.26.2.305. The application and proofs below are
self-contained, and do not claim a new monotonicity principle.

This permits an entire patch, rather than a single vertex, to be optimized at
all thresholds of one ordering. It supplies no quantitative lower bound on the
saving; that remains necessary for an improved circuit coefficient.
-/

@[expose] public section

namespace Frontier.PatchLayout

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A new cut agrees with the old cut outside the patch. -/
def AgreesOutside (patch boundary candidate : Finset V) : Prop :=
  ∀ v, v ∉ patch → (v ∈ candidate ↔ v ∈ boundary)

/-- An optimal choice of the vertices inside a patch. -/
def IsMinimum (cost : Finset V → ℕ) (patch boundary candidate : Finset V) : Prop :=
  AgreesOutside patch boundary candidate ∧
    ∀ other, AgreesOutside patch boundary other → cost candidate ≤ cost other

variable (cost : Finset V → ℕ)

omit [Fintype V] [DecidableEq V] in
private theorem exists_minimum [Finite V] (patch boundary : Finset V) :
    ∃ candidate, IsMinimum cost patch boundary candidate := by
  classical
  let _ := Fintype.ofFinite V
  let feasible := univ.filter (AgreesOutside patch boundary)
  have hb : boundary ∈ feasible := mem_filter.mpr ⟨mem_univ _, fun _ _ => Iff.rfl⟩
  obtain ⟨candidate, hc, hmin⟩ := feasible.exists_min_image cost ⟨_, hb⟩
  exact ⟨candidate, (mem_filter.mp hc).2,
    fun other ho => hmin other (mem_filter.mpr ⟨mem_univ _, ho⟩)⟩

omit [Fintype V] in
private theorem agrees_inter_union {patch X Y A B : Finset V} (hXY : X ⊆ Y)
    (hA : AgreesOutside patch X A) (hB : AgreesOutside patch Y B) :
    AgreesOutside patch X (A ∩ B) ∧ AgreesOutside patch Y (A ∪ B) := by
  constructor <;> intro v hv
  · simp only [mem_inter, hA v hv, hB v hv]
    exact ⟨And.left, fun hx => ⟨hx, hXY hx⟩⟩
  · simp only [mem_union, hA v hv, hB v hv]
    exact ⟨fun h => h.elim (hXY ·) id, Or.inr⟩

omit [Fintype V] in
/-- Uncrossing two optimal cuts preserves optimality of their union at the later boundary. -/
theorem IsMinimum.union
    (hsub : ∀ A B, cost (A ∩ B) + cost (A ∪ B) ≤ cost A + cost B)
    {patch X Y A B : Finset V} (hXY : X ⊆ Y)
    (hA : IsMinimum cost patch X A) (hB : IsMinimum cost patch Y B) :
    IsMinimum cost patch Y (A ∪ B) := by
  obtain ⟨hi, hu⟩ := agrees_inter_union hXY hA.1 hB.1
  refine ⟨hu, fun other ho => ?_⟩
  have h := hsub A B
  have hleft := hA.2 _ hi
  have hright := hB.2 other ho
  lia

omit [Fintype V] in
/-- The largest minimizer contains every minimizer with the same boundary. -/
theorem exists_largest_minimum [Finite V]
    (hsub : ∀ A B, cost (A ∩ B) + cost (A ∪ B) ≤ cost A + cost B)
    (patch boundary : Finset V) :
    ∃ candidate, IsMinimum cost patch boundary candidate ∧
      ∀ other, IsMinimum cost patch boundary other → other ⊆ candidate := by
  classical
  let _ := Fintype.ofFinite V
  obtain ⟨first, hfirst⟩ := exists_minimum cost patch boundary
  let minima := univ.filter (IsMinimum cost patch boundary)
  have hf : first ∈ minima := mem_filter.mpr ⟨mem_univ _, hfirst⟩
  obtain ⟨candidate, hc, hmax⟩ := minima.exists_max_image card ⟨_, hf⟩
  have hcandidate := (mem_filter.mp hc).2
  refine ⟨candidate, hcandidate, fun other ho => ?_⟩
  have hu := IsMinimum.union cost hsub (Subset.refl boundary) ho hcandidate
  have hcard := hmax (other ∪ candidate) (mem_filter.mpr ⟨mem_univ _, hu⟩)
  have heq : other ∪ candidate = candidate :=
    (eq_of_subset_of_card_le subset_union_right hcard).symm
  exact heq ▸ subset_union_left

/-- Choose the largest minimum-cost replacement of a patch. -/
noncomputable def largestMinimum
    (hsub : ∀ A B, cost (A ∩ B) + cost (A ∪ B) ≤ cost A + cost B)
    (patch boundary : Finset V) : Finset V :=
  (exists_largest_minimum cost hsub patch boundary).choose

theorem largestMinimum_spec
    (hsub : ∀ A B, cost (A ∩ B) + cost (A ∪ B) ≤ cost A + cost B)
    (patch boundary : Finset V) :
    IsMinimum cost patch boundary (largestMinimum cost hsub patch boundary) ∧
      ∀ other, IsMinimum cost patch boundary other →
        other ⊆ largestMinimum cost hsub patch boundary :=
  (exists_largest_minimum cost hsub patch boundary).choose_spec

/-- Nested boundary conditions give nested optimal cuts. -/
theorem largestMinimum_monotone
    (hsub : ∀ A B, cost (A ∩ B) + cost (A ∪ B) ≤ cost A + cost B)
    (patch : Finset V) : Monotone (largestMinimum cost hsub patch) := by
  intro X Y hXY
  have hX := largestMinimum_spec cost hsub patch X
  have hY := largestMinimum_spec cost hsub patch Y
  exact subset_union_left.trans (hY.2 _ (IsMinimum.union cost hsub hXY hX.1 hY.1))

/-- Preserve the empty cut, and otherwise use the largest minimizer. For a cut cost
vanishing at the empty set, this is still optimal. The endpoint convention makes
the resulting nested cuts representable by real vertex keys. -/
noncomputable def improve
    (hsub : ∀ A B, cost (A ∩ B) + cost (A ∪ B) ≤ cost A + cost B)
    (patch boundary : Finset V) : Finset V :=
  if boundary = ∅ then ∅ else largestMinimum cost hsub patch boundary

theorem improve_spec
    (hsub : ∀ A B, cost (A ∩ B) + cost (A ∪ B) ≤ cost A + cost B)
    (hzero : cost ∅ = 0) (patch boundary : Finset V) :
    IsMinimum cost patch boundary (improve cost hsub patch boundary) := by
  by_cases h : boundary = ∅
  · subst boundary
    simp only [improve, ite_true]
    exact ⟨fun _ _ => Iff.rfl, fun _ _ => by rw [hzero]; exact Nat.zero_le _⟩
  · simpa [improve, h] using (largestMinimum_spec cost hsub patch boundary).1

theorem improve_monotone
    (hsub : ∀ A B, cost (A ∩ B) + cost (A ∪ B) ≤ cost A + cost B)
    (patch : Finset V) : Monotone (improve cost hsub patch) := by
  intro X Y hXY
  by_cases hX : X = ∅
  · simp [improve, hX]
  have hY : Y ≠ ∅ := fun h => hX (subset_empty.mp (h ▸ hXY))
  simpa [improve, hX, hY] using largestMinimum_monotone cost hsub patch hXY

@[simp] theorem improve_empty
    (hsub : ∀ A B, cost (A ∩ B) + cost (A ∪ B) ≤ cost A + cost B)
    (patch : Finset V) : improve cost hsub patch ∅ = ∅ := by
  simp [improve]

theorem improve_univ
    (hsub : ∀ A B, cost (A ∩ B) + cost (A ∪ B) ≤ cost A + cost B)
    (hfull : cost univ = 0) (patch : Finset V) : improve cost hsub patch univ = univ := by
  by_cases h : (univ : Finset V) = ∅
  · simp [h]
  rw [improve, ite_eq_right h]
  apply Subset.antisymm (subset_univ _)
  apply (largestMinimum_spec cost hsub patch univ).2
  exact ⟨fun _ _ => Iff.rfl, fun _ _ => by rw [hfull]; exact Nat.zero_le _⟩

omit cost [DecidableEq V] in
/-- Every monotone transformation of cuts preserving both endpoints has a representation
by new vertex keys. The new keys can be chosen from the original keys. -/
theorem exists_key_of_monotone (Φ : Finset V → Finset V) (hmono : Monotone Φ)
    (hzero : Φ ∅ = ∅) (hfull : Φ univ = univ) (key : V → ℝ) :
    ∃ key' : V → ℝ, (∀ v, key' v ∈ Set.range key) ∧
      ∀ t, univ.filter (fun v => key' v < t) = Φ (univ.filter (fun v => key v < t)) := by
  classical
  have one (v : V) : ∃ value : ℝ, value ∈ Set.range key ∧
      ∀ t, value < t ↔ v ∈ Φ (univ.filter (fun v => key v < t)) := by
    let S := univ.filter fun w => v ∈ Φ (univ.filter fun u => key u ≤ key w)
    have hS : S.Nonempty := by
      obtain ⟨w, _, hw⟩ := univ.exists_max_image key ⟨v, mem_univ _⟩
      refine ⟨w, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
      rw [filter_true_of_mem hw, hfull]
      exact mem_univ _
    obtain ⟨w, hw, hmin⟩ := S.exists_min_image key hS
    refine ⟨key w, ⟨w, rfl⟩, fun t => ⟨?_, ?_⟩⟩
    · intro hwt
      apply hmono (show univ.filter (fun u => key u ≤ key w) ⊆
          univ.filter (fun u => key u < t) from ?_) (mem_filter.mp hw).2
      intro u hu
      exact mem_filter.mpr ⟨mem_univ _, lt_of_le_of_lt (mem_filter.mp hu).2 hwt⟩
    · intro hv
      let cut := univ.filter fun u => key u < t
      have hc : cut.Nonempty := by
        by_contra h
        have he : cut = ∅ := not_nonempty_iff_eq_empty.mp h
        change v ∈ Φ cut at hv
        rw [he, hzero] at hv
        exact notMem_empty _ hv
      obtain ⟨z, hz, hmax⟩ := cut.exists_max_image key hc
      have hzS : z ∈ S := by
        refine mem_filter.mpr ⟨mem_univ _, hmono ?_ hv⟩
        intro u hu
        exact mem_filter.mpr ⟨mem_univ _, hmax u hu⟩
      exact lt_of_le_of_lt (hmin z hzS) (mem_filter.mp hz).2
  choose key' hrange hkey using one
  refine ⟨key', hrange, fun t => ?_⟩
  ext v
  simpa using hkey v t

/-- One set of real keys optimizes every threshold cut inside the chosen patch, while
fixing all outside keys. Different thresholds need not choose their minimizers independently. -/
theorem exists_key_minimum
    (hsub : ∀ A B, cost (A ∩ B) + cost (A ∪ B) ≤ cost A + cost B)
    (hzero : cost ∅ = 0) (hfull : cost univ = 0) (patch : Finset V) (key : V → ℝ) :
    ∃ key' : V → ℝ, (∀ v, v ∉ patch → key' v = key v) ∧
      (∀ v, key' v ∈ Set.range key) ∧ ∀ t,
        IsMinimum cost patch (univ.filter fun v => key v < t)
          (univ.filter fun v => key' v < t) := by
  obtain ⟨key', hrange, hkey⟩ := exists_key_of_monotone (improve cost hsub patch)
    (improve_monotone cost hsub patch) (improve_empty cost hsub patch)
    (improve_univ cost hsub hfull patch) key
  have hmin (t : ℝ) : IsMinimum cost patch (univ.filter fun v => key v < t)
      (univ.filter fun v => key' v < t) := by
    rw [hkey t]
    exact improve_spec cost hsub hzero patch _
  refine ⟨key', fun v hv => ?_, hrange, hmin⟩
  have hiff (t : ℝ) : key' v < t ↔ key v < t := by simpa using (hmin t).1 v hv
  apply le_antisymm
  · by_contra! h
    exact lt_irrefl _ ((hiff (key' v)).mpr h)
  · by_contra! h
    exact lt_irrefl _ ((hiff (key v)).mp h)

omit cost in
/-- A local key update has bounded ties when each original vertex can supply a key
to only a bounded number of updated vertices. This bound is independent of the graph size. -/
theorem card_ties_le_of_local (key key' : V → ℝ) (scope : V → Finset V) {M L : ℕ}
    (hlocal : ∀ v, ∃ u ∈ scope v, key' v = key u)
    (hload : ∀ u, (univ.filter fun v => u ∈ scope v).card ≤ L)
    (htie : ∀ a, (univ.filter fun v => key v = a).card ≤ M) (a : ℝ) :
    (univ.filter fun v => key' v = a).card ≤ M * L := by
  classical
  let sources := univ.filter fun u => key u = a
  have hsub : univ.filter (fun v => key' v = a) ⊆
      sources.biUnion (fun u => univ.filter fun v => u ∈ scope v) := by
    intro v hv
    obtain ⟨u, hu, he⟩ := hlocal v
    refine mem_biUnion.mpr ⟨u, mem_filter.mpr ⟨mem_univ _, ?_⟩,
      mem_filter.mpr ⟨mem_univ _, hu⟩⟩
    exact he.symm.trans (mem_filter.mp hv).2
  calc (univ.filter fun v => key' v = a).card
      ≤ (sources.biUnion fun u => univ.filter fun v => u ∈ scope v).card := card_le_card hsub
    _ ≤ ∑ u ∈ sources, (univ.filter fun v => u ∈ scope v).card := card_biUnion_le
    _ ≤ ∑ _u ∈ sources, L := sum_le_sum fun u _ => hload u
    _ = sources.card * L := by simp
    _ ≤ M * L := Nat.mul_le_mul_right L (htie a)

end Frontier.PatchLayout

namespace Frontier.Hypergraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [Finite E] (H : Hypergraph V E)

omit [DecidableEq V] in
/-- Exact local optimization of hypergraph boundary size, simultaneously for all
thresholds of one real-key ordering. Hyperedges may have arbitrary arity. -/
theorem exists_key_patch_minimum (patch : Finset V) (key : V → ℝ) :
    ∃ key' : V → ℝ, (∀ v, v ∉ patch → key' v = key v) ∧
      (∀ v, key' v ∈ Set.range key) ∧ ∀ t,
        PatchLayout.IsMinimum (fun A : Finset V => (H.cut (A : Set V)).ncard) patch
          (Finset.univ.filter fun v => key v < t) (Finset.univ.filter fun v => key' v < t) := by
  classical
  apply PatchLayout.exists_key_minimum
  · intro A B
    simpa using H.ncard_cut_submodular (A : Set V) (B : Set V)
  · simp
  · simp

omit [Fintype V] [DecidableEq V] in
/-- Changing only the vertices in `D` creates at most their total number of incident
hyperedges. This bound also accounts for prefixes splitting a group of tied keys. -/
theorem ncard_cut_le_of_agrees (X Y : Set V) (D : Finset V) {d : ℕ}
    (hdegree : ∀ v, {e | v ∈ H e}.ncard ≤ d)
    (hagree : ∀ v, v ∉ D → (v ∈ X ↔ v ∈ Y)) :
    (H.cut X).ncard ≤ (H.cut Y).ncard + d * D.card := by
  classical
  let _ := Fintype.ofFinite E
  let incident (v : V) : Finset E := Finset.univ.filter fun e => v ∈ H e
  have hsub : H.cut X ⊆ H.cut Y ∪ (↑(D.biUnion incident) : Set E) := by
    intro e he
    by_cases h : ∃ v ∈ D, v ∈ H e
    · obtain ⟨v, hv, hve⟩ := h
      exact Or.inr (Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hve⟩⟩)
    · obtain ⟨⟨u, hue, huX⟩, v, hve, hvX⟩ := he
      have huD : u ∉ D := fun hu => h ⟨u, hu, hue⟩
      have hvD : v ∉ D := fun hv => h ⟨v, hv, hve⟩
      exact Or.inl ⟨⟨u, hue, (hagree u huD).mp huX⟩,
        v, hve, fun hvY => hvX ((hagree v hvD).mpr hvY)⟩
  have hcard : (D.biUnion incident).card ≤ d * D.card := by
    calc (D.biUnion incident).card ≤ ∑ v ∈ D, (incident v).card := Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ D, d := Finset.sum_le_sum fun v _ => by
        simpa [incident, ← Set.ncard_coe_finset] using hdegree v
      _ = d * D.card := by simp [Nat.mul_comm]
  calc (H.cut X).ncard ≤ (H.cut Y ∪ (↑(D.biUnion incident) : Set E)).ncard :=
        Set.ncard_le_ncard hsub
    _ ≤ (H.cut Y).ncard + (↑(D.biUnion incident) : Set E).ncard := Set.ncard_union_le _ _
    _ ≤ (H.cut Y).ncard + d * D.card := by
        simpa only [Set.ncard_coe_finset] using Nat.add_le_add_left hcard _

omit [DecidableEq V] in
/-- Threshold bounds become bounds for every prefix after paying for tied keys.
Without the tie bound, even constant keys would have zero threshold cost. -/
theorem exists_key_cut_le (score : V → ℝ) {d B M : ℕ}
    (hdegree : ∀ v, {e | v ∈ H e}.ncard ≤ d)
    (hbound : ∀ t, (H.cut {v | score v < t}).ncard ≤ B)
    (htie : ∀ a, (Finset.univ.filter fun v => score v = a).card ≤ M) :
    ∃ key : V → ℕ, Function.Injective key ∧
      ∀ t, (H.cut {v | key v < t}).ncard ≤ B + d * M := by
  classical
  obtain ⟨key, hinj, hsort⟩ := Frontier.exists_key_of_score score
  refine ⟨key, hinj, fun t => ?_⟩
  rcases hsort t with hempty | ⟨m, hin, hout⟩
  · have he : {v | key v < t} = (∅ : Set V) := Set.eq_empty_iff_forall_notMem.mpr hempty
    simp [he]
  · have hagree : ∀ v, v ∉ Finset.univ.filter (fun v => score v = m) →
        (v ∈ {v | key v < t} ↔ v ∈ {v | score v < m}) := by
      intro v hv
      have hne : score v ≠ m := by simpa using hv
      constructor
      · intro h
        exact lt_of_le_of_ne (hin v h) hne
      · intro h
        by_contra hn
        exact (not_lt_of_ge (hout v hn)) h
    exact (H.ncard_cut_le_of_agrees _ _ _ hdegree hagree).trans
      (Nat.add_le_add (hbound m) (Nat.mul_le_mul_left d (htie m)))

omit [DecidableEq V] in
/-- Per-threshold patch certificates yield one ordering controlling all prefixes.
Only the vertices of the patch can add to an original tie group. -/
theorem exists_key_patch_cut_le (patch : Finset V) (score : V → ℝ) {d B M : ℕ}
    (hdegree : ∀ v, {e | v ∈ H e}.ncard ≤ d)
    (htie : ∀ a, (Finset.univ.filter fun v => score v = a).card ≤ M)
    (hsupply : ∀ t, ∃ A : Finset V,
      PatchLayout.AgreesOutside patch (Finset.univ.filter fun v => score v < t) A ∧
        (H.cut (A : Set V)).ncard ≤ B) :
    ∃ key : V → ℕ, Function.Injective key ∧
      ∀ t, (H.cut {v | key v < t}).ncard ≤ B + d * (M + patch.card) := by
  classical
  obtain ⟨score', hfix, _, hmin⟩ := H.exists_key_patch_minimum patch score
  apply H.exists_key_cut_le score' hdegree
  · intro t
    obtain ⟨A, hA, hbound⟩ := hsupply t
    simpa using ((hmin t).2 A hA).trans hbound
  · intro a
    have hsub : Finset.univ.filter (fun v => score' v = a) ⊆
        (Finset.univ.filter fun v => score v = a) ∪ patch := by
      intro v hv
      by_cases hp : v ∈ patch
      · exact Finset.mem_union_right _ hp
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (hfix v hp).symm.trans (Finset.mem_filter.mp hv).2⟩)
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (htie a) _))

variable {ι F Z : Type*} [Field F] [AddCommGroup Z] [Module F Z] [FiniteDimensional F Z]

/-- Count the signal boundary and the consistency syndrome together in one objective.
The two costs are added here; the joint-observation code can further reduce overlaps. -/
noncomputable def cutAndSyndrome (L : Z →ₗ[F] (ι → F)) (site : ι → V) (X : Set V) : ℕ :=
  (H.cut X).ncard + LinearBoundary.syndromeRank L (site ⁻¹' X)

omit [DecidableEq V] in
/-- Parity consistency and signal boundaries admit a common patch optimization.
This is an ordering certificate, without a bound in terms of surplus gate count. -/
theorem exists_key_patch_syndrome_minimum
    (L : Z →ₗ[F] (ι → F)) (site : ι → V) (patch : Finset V) (key : V → ℝ) :
    ∃ key' : V → ℝ, (∀ v, v ∉ patch → key' v = key v) ∧
      (∀ v, key' v ∈ Set.range key) ∧ ∀ t,
        PatchLayout.IsMinimum (fun A : Finset V => H.cutAndSyndrome L site A) patch
          (Finset.univ.filter fun v => key v < t) (Finset.univ.filter fun v => key' v < t) := by
  classical
  apply PatchLayout.exists_key_minimum
  · intro A B
    have hh := H.ncard_cut_submodular (A : Set V) (B : Set V)
    have hs := LinearBoundary.syndromeRank_submodular L
      (site ⁻¹' (A : Set V)) (site ⁻¹' (B : Set V))
    simp only [cutAndSyndrome, Finset.coe_inter, Finset.coe_union,
      Set.preimage_inter, Set.preimage_union]
    lia
  · simp [cutAndSyndrome]
  · simp [cutAndSyndrome]

end Frontier.Hypergraph
