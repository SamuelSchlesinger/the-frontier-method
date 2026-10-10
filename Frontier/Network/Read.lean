/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Network

/-!
# Discarding unread network inputs

Restrict a constraint network to the coordinates it reads. This leaves its graph
and local edge constraints unchanged, and every remaining input is read. The
construction uses zero on discarded coordinates; locality proves that the choice
does not affect acceptance.
-/

@[expose] public section

namespace Frontier.Network

open Set

variable {U ι V E : Type*} [Zero U] (N : Network U ι V E)

open Classical in
/-- Extend the read input values by zero on all unused coordinates. -/
noncomputable def extendRead (x : N.read → U) : ι → U := fun i =>
  if hi : i ∈ N.read then x ⟨i, hi⟩ else 0

@[simp] theorem extendRead_apply (x : N.read → U) (i : N.read) :
    N.extendRead x i = x i := by simp [extendRead, i.2]

/-- Remove unused input coordinates without changing the constraint graph. -/
noncomputable def restrictRead : Network U N.read V E where
  toMultigraph := N.toMultigraph
  site i := N.site i
  Check v x α := N.Check v (N.extendRead x) α
  check_local v x y α β hin hed hx := by
    apply N.check_local v _ _ α β ?_ hed hx
    intro i hi
    have hread : i ∈ N.read := ⟨v, mem_univ v, hi⟩
    simpa only [← N.extendRead_apply x ⟨i, hread⟩,
      ← N.extendRead_apply y ⟨i, hread⟩] using hin ⟨i, hread⟩ hi

/-- Restricting to the read coordinates preserves acceptance of every input. -/
theorem mem_accepted_restrictRead (x : ι → U) :
    (fun i : N.read => x i) ∈ N.restrictRead.accepted ↔ x ∈ N.accepted := by
  change N.extendRead (fun i : N.read => x i) ∈ N.accepted ↔ x ∈ N.accepted
  exact iff_of_eq (N.dependsOn_read fun i hi => N.extendRead_apply _ ⟨i, hi⟩)

@[simp] theorem read_restrictRead : N.restrictRead.read = univ := by
  ext i
  simp only [mem_univ, iff_true]
  obtain ⟨v, hv, hi⟩ := i.2
  exact ⟨v, hv, hi⟩

/-- Restriction does not increase the number of inputs read at a vertex. -/
theorem ncard_readAt_restrictRead_le [Finite ι] (v : V) :
    (N.restrictRead.readAt v).ncard ≤ (N.readAt v).ncard := by
  refine ncard_le_ncard_of_injOn Subtype.val (fun _ h => h)
    (fun _ _ _ _ h => Subtype.ext h) (toFinite _)

end Frontier.Network
