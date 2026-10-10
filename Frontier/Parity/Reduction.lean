/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Parity.Network

/-!
# Circuit reduction with free linear inputs

For a circuit reading linear forms of the independent input, write `c` for the
redundancy of the forms actually read. The compiler gives
`cycleRank + c ≤ (fanin - 1) * size - dimension + log_q K + 1`,
and every layout satisfies
`log_q |S| ≤ width + c + 3 log_q K + log_q (vertices + 1) + fanin + 2`.
These are separate inequalities: the positive consistency term in the second
does not cancel the redundancy in the first at a layout coefficient below one.
-/

@[expose] public section

namespace Frontier

open Set Module LinearBoundary Cslib.Circuits

variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {σ : Signature} {m : ℕ}
  (I : Interpretation σ F) (Acc : Set F) (c : Circuit σ m 1)
  (L : V →ₗ[F] (Fin m → F)) {S : Set V} {K r : ℕ}

/-- The cycle bound retains the redundancy of reached supplied inputs. -/
theorem cycleRank_add_redundancy_le_of_linear_inputs (hfan : c.FanInAtMost r)
    (hS : SumsetFree S K) (hK : K ≤ S.ncard)
    (hc : ∀ x, c.eval I (L x) 0 ∈ Acc ↔ x ∈ S) :
    ((constraintNetwork I Acc c).cycleRank : ℝ) +
      (constraintNetwork I Acc c).readRedundancy L ≤
      ((r - 1) * c.innerSize : ℕ) - finrank F V + Real.logb (Nat.card F) K + 1 := by
  set N := constraintNetwork I Acc c
  set d := coordinateRank L N.read
  have hq : (1 : ℝ) < Nat.card F := by exact_mod_cast Finite.one_lt_card
  have hKpos : 0 < K := by
    have h := hS ∅ ∅ (by simp)
    simpa using h
  have hnull : ((finrank F V - d : ℕ) : ℝ) < Real.logb (Nat.card F) K := by
    rw [Real.lt_logb_iff_rpow_lt hq (by exact_mod_cast hKpos), Real.rpow_natCast]
    exact_mod_cast pow_sub_read_rank_lt_of_linear_inputs I Acc c L hS hK hc
  have hdim : ((finrank F V - d : ℕ) : ℝ) + d = finrank F V := by
    exact_mod_cast Nat.sub_add_cancel (LinearMap.finrank_range_le (coordinateMap L N.read))
  have hgraph : (N.cycleRank : ℝ) + d + N.readRedundancy L ≤
      ((r - 1) * c.innerSize : ℕ) + 1 := by
    exact_mod_cast cycleRank_add_read_rank_add_redundancy_le I Acc c L hfan
  linarith

/-- The width demand on the original independent accepting set, with the
consistency cost of reached supplied inputs shown explicitly. -/
theorem logb_ncard_le_of_linear_inputs [Finite V] (hr : 2 ≤ r) (hfan : c.FanInAtMost r)
    (hS : SumsetFree S K) (hbig : K ^ 2 ≤ S.ncard)
    (hc : ∀ x, c.eval I (L x) 0 ∈ Acc ↔ x ∈ S)
    (π : Layout (Compiler.Vertex c.program c.outputs)) {w : ℕ}
    (hw : ∀ t, ((constraintNetwork I Acc c).cut (π.initial t)).ncard ≤ w) :
    Real.logb (Nat.card F) S.ncard ≤ w + (r + 2) +
      (constraintNetwork I Acc c).readRedundancy L +
        3 * Real.logb (Nat.card F) K +
          Real.logb (Nat.card F) (Nat.card (Compiler.Vertex c.program c.outputs) + 1) := by
  have hN : ∀ x, L x ∈ (constraintNetwork I Acc c).accepted ↔ x ∈ S := by
    intro x
    rw [Compiler.accepted_network]
    change (∀ o : Fin 1, c.eval I (L x) o ∈ Acc) ↔ x ∈ S
    rw [← hc x]
    exact ⟨fun h => h 0, fun h o => Subsingleton.elim o 0 ▸ h⟩
  have h := (constraintNetwork I Acc c).logb_ncard_le_of_linear_inputs L hS hbig hN π hw
    (Compiler.maxDegreeLE I _ hr hfan) (Compiler.ncard_readAt_le I _)
  convert h using 1
  dsimp only [Network.readRedundancy]
  push_cast
  ring

end Frontier
