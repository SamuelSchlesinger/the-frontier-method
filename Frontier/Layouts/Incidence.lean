/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.Local
import Mathlib.Tactic.NormNum

/-!
# Signing incidence vectors cannot improve a fixed family of cuts

For oriented vertex-incidence vectors, the squared Euclidean norm of a signed sum over a
region is its edge boundary plus four times the number of internal edges with opposite
signs. Consequently, a simultaneous signed-prefix bound is equivalent to the same bound
on the original cuts. This obstructs a direct incidence-vector specialization of the
signed-prefix route to the Euclidean Steinitz theorem; it does not obstruct reordering.

The two sign classes can still be reordered positive-forward and negative-reverse, as in
Chobanyan's transference argument. `cutSize_split` records their exact boundary accounting.
Loops contribute zero throughout, and parallel edges retain their multiplicities.
-/

@[expose] public section

namespace Frontier.Multigraph

open Finset

variable {V E : Type*} [Fintype E] (G : Multigraph V E)

open Classical in
/-- The oriented incidence vector of a vertex, with one real coordinate per edge. -/
noncomputable def incidenceVector (v : V) (e : E) : ℝ :=
  (if G.src e = v then 1 else 0) - (if G.tgt e = v then 1 else 0)

/-- Squared Euclidean norm of the incidence sum with vertex coefficients `a`. -/
def incidenceEnergy (a : V → ℝ) : ℝ :=
  ∑ e, (a (G.src e) - a (G.tgt e)) ^ 2

/-- A signed indicator: zero outside the region and either one or minus one inside. -/
def signedIndicator (region sign : V → Bool) (v : V) : ℝ :=
  if region v then if sign v then 1 else -1 else 0

/-- Internal edges of a region whose endpoints have different signs. -/
def internalSignCut (region sign : V → Bool) : ℕ :=
  ∑ e, if region (G.src e) && region (G.tgt e) then G.crossing sign e else 0

omit [Fintype E] in
/-- The coordinate formula really is the sum of the vertex-incidence vectors. -/
theorem sum_incidenceVector [Fintype V] (a : V → ℝ) (e : E) :
    (∑ v, a v * G.incidenceVector v e) = a (G.src e) - a (G.tgt e) := by
  classical
  simp [incidenceVector, mul_sub, mul_ite, Finset.sum_sub_distrib]

/-- Exact signed energy: boundary edges cost one and discordant internal edges cost four. -/
theorem incidenceEnergy_signedIndicator (region sign : V → Bool) :
    G.incidenceEnergy (signedIndicator region sign) =
      G.cutSize region + 4 * (G.internalSignCut region sign : ℝ) := by
  simp only [incidenceEnergy, cutSize, internalSignCut, Nat.cast_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  cases hr : region (G.src e) <;> cases ht : region (G.tgt e) <;>
    cases hs : sign (G.src e) <;> cases hu : sign (G.tgt e) <;>
    norm_num [signedIndicator, crossing, hr, ht, hs, hu]

/-- Every signing has at least the energy of the unsigned cut. -/
theorem cutSize_le_incidenceEnergy (region sign : V → Bool) :
    (G.cutSize region : ℝ) ≤ G.incidenceEnergy (signedIndicator region sign) := by
  rw [incidenceEnergy_signedIndicator]
  exact le_add_of_nonneg_right (by positivity)

/-- Constant signs attain the unsigned energy for every region simultaneously. -/
theorem incidenceEnergy_constantSign (region : V → Bool) :
    G.incidenceEnergy (signedIndicator region fun _ => true) = G.cutSize region := by
  simp [incidenceEnergy_signedIndicator, internalSignCut, crossing]

/-- Signing cannot improve any prescribed family of cuts, including all layout prefixes. -/
theorem exists_signed_incidence_bound_iff {ι : Type*} (region : ι → V → Bool)
    (bound : ι → ℝ) :
    (∃ sign : V → Bool, ∀ i,
      G.incidenceEnergy (signedIndicator (region i) sign) ≤ bound i) ↔
      ∀ i, (G.cutSize (region i) : ℝ) ≤ bound i := by
  constructor
  · rintro ⟨sign, h⟩ i
    exact (G.cutSize_le_incidenceEnergy (region i) sign).trans (h i)
  · intro h
    exact ⟨fun _ => true, fun i => by simpa [incidenceEnergy_constantSign] using h i⟩

/-- Splitting a region into its two sign classes counts internal crossing edges twice. -/
theorem cutSize_split (region sign : V → Bool) :
    G.cutSize (fun v => region v && sign v) +
      G.cutSize (fun v => region v && !sign v) =
        G.cutSize region + 2 * G.internalSignCut region sign := by
  simp only [cutSize, internalSignCut, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  cases hr : region (G.src e) <;> cases ht : region (G.tgt e) <;>
    cases hs : sign (G.src e) <;> cases hu : sign (G.tgt e) <;>
    simp [crossing, hr, ht, hs, hu]

/-- At least one sign class retains half the original boundary. -/
theorem cutSize_le_two_mul_max_split (region sign : V → Bool) :
    G.cutSize region ≤ 2 * max (G.cutSize fun v => region v && sign v)
      (G.cutSize fun v => region v && !sign v) := by
  have h := G.cutSize_split region sign
  have hp := le_max_left (G.cutSize fun v => region v && sign v)
    (G.cutSize fun v => region v && !sign v)
  have hm := le_max_right (G.cutSize fun v => region v && sign v)
    (G.cutSize fun v => region v && !sign v)
  lia

end Frontier.Multigraph
