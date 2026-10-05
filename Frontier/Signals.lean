/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Compiler

/-!
# Frontiers measured by distinct circuit signals

The compiler labels every edge by the wire it carries. Exactness makes all edges with the
same label equal on every accepting run. `ncard_accepted_le_signals` therefore charges only
the distinct signals on the union of adjacent frontiers, together with the input read at the
step. This is a capacity theorem, not a new universal layout bound.
-/

@[expose] public section

namespace Frontier.Compiler

open Cslib.Circuits Set

variable {σ : Signature} {n s : ℕ} {O U : Type*} [Finite O] [Finite U] [Nonempty U]
  {p : Program σ n s} {out : O → Wire n s} (I : Interpretation σ U) (Acc : O → Set U)

/-- The signal labels on a frontier. Repeated edges of the same wire are charged once. -/
noncomputable def signalFrontier (π : Layout (Vertex p out)) (t : ℕ) : Set (Signal p out) :=
  Edge.signal '' (network p out I Acc).frontier π t

omit [Finite U] [Nonempty U] in
/-- Signal capacity never exceeds edge capacity. -/
theorem ncard_signalFrontier_le (π : Layout (Vertex p out)) (t : ℕ) :
    (signalFrontier I Acc π t).ncard ≤ ((network p out I Acc).frontier π t).ncard :=
  ncard_image_le (toFinite _)

/-- **Counting with signal capacity.** The step budget charges distinct signals across both
frontiers and the inputs read at the vertex. It can be strictly smaller than the edge budget. -/
theorem ncard_accepted_le_signals (π : Layout (Vertex p out)) {K b : ℕ}
    (hfree : RectangleFree (network p out I Acc).accepted K)
    (hK : K ≤ (network p out I Acc).accepted.ncard)
    (hb : ∀ t, ∀ ht : t < Nat.card (Vertex p out),
      (signalFrontier I Acc π t ∪ signalFrontier I Acc π (t + 1)).ncard +
        ((network p out I Acc).readAt (π.symm ⟨t, ht⟩)).ncard ≤ b) :
    (network p out I Acc).accepted.ncard ≤ (K - 1) ^ 2 *
      (Nat.card (Vertex p out) * Nat.card U ^ b +
        Nat.card U ^ (network p out I Acc).readᶜ.ncard) := by
  apply (network p out I Acc).ncard_accepted_le_labels π Edge.signal
    (fun x w => p.trace I x w.1)
    (fun _ hx e => eq_trace ((network p out I Acc).satisfies_witness hx) e) hfree hK
  simpa only [image_union, signalFrontier] using hb

end Frontier.Compiler
