/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Parity
public import Frontier.Reduction

/-!
# Independent information read from supplied linear inputs

A network receiving linear forms of an independent input depends only on the
forms it actually reads. If its promised accepting set is large and sumset-free,
the common kernel of those forms has fewer than `K` elements. Thus their rank is
at least the independent input dimension minus `log_q K`.

The compiler counts physical input ports, whereas this support bound counts
independent forms. Both counts are retained: their difference is the redundancy
of the read inputs. No correctness on inconsistent supplied inputs is required.
-/

@[expose] public section

namespace Frontier

open Set Module Cslib.Circuits

variable {F V W ι : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

/-- A linear observation of a large sumset-free set has a small kernel. -/
theorem SumsetFree.pow_finrank_ker_lt [FiniteDimensional F V]
    {S : Set V} {K : ℕ} (hS : SumsetFree S K) (hK : K ≤ S.ncard)
    (L : V →ₗ[F] W)
    (hobs : ∀ x y, L x = L y → (x ∈ S ↔ y ∈ S)) :
    Nat.card F ^ finrank F (LinearMap.ker L) < K := by
  have h := hS.ncard_lt_of_stable hK (H := LinearMap.ker L) (by
    intro x hx y hy
    exact (hobs x (x + y) (by rw [L.map_add, LinearMap.mem_ker.mp hy, add_zero])).mp hx)
  rw [← Nat.card_coe_set_eq] at h
  change Nat.card ↥(LinearMap.ker L) < K at h
  rwa [Module.natCard_eq_pow_finrank (K := F)] at h

/-- The common kernel of the supplied forms a network reads is small. -/
theorem Network.pow_finrank_read_ker_lt {J E : Type*} [FiniteDimensional F V]
    (N : Network F ι J E) (L : V →ₗ[F] (ι → F)) {S : Set V} {K : ℕ}
    (hS : SumsetFree S K) (hK : K ≤ S.ncard)
    (hN : ∀ x, L x ∈ N.accepted ↔ x ∈ S) :
    Nat.card F ^ finrank F (LinearMap.ker (LinearBoundary.coordinateMap L N.read)) < K := by
  apply hS.pow_finrank_ker_lt hK (LinearBoundary.coordinateMap L N.read)
  intro x y hxy
  rw [← hN x, ← hN y]
  exact iff_of_eq (N.dependsOn_read fun i hi => congrFun hxy ⟨i, hi⟩)

/-- Read forms span all but fewer than `log_q K` of the independent input
dimensions. The exponent refers to rank, not to the number of supplied ports. -/
theorem Network.pow_sub_read_rank_lt {J E : Type*} [FiniteDimensional F V]
    (N : Network F ι J E) (L : V →ₗ[F] (ι → F)) {S : Set V} {K : ℕ}
    (hS : SumsetFree S K) (hK : K ≤ S.ncard)
    (hN : ∀ x, L x ∈ N.accepted ↔ x ∈ S) :
    Nat.card F ^ (finrank F V - LinearBoundary.coordinateRank L N.read) < K := by
  have hr := (LinearBoundary.coordinateMap L N.read).finrank_range_add_finrank_ker
  have heq : finrank F V - LinearBoundary.coordinateRank L N.read =
      finrank F (LinearMap.ker (LinearBoundary.coordinateMap L N.read)) := by
    dsimp [LinearBoundary.coordinateRank]
    lia
  rw [heq]
  exact N.pow_finrank_read_ker_lt L hS hK hN

namespace LinearBoundary

/-- Independent read information never exceeds the physical read count. -/
theorem coordinateRank_le_ncard [Finite ι] (L : V →ₗ[F] (ι → F)) (Q : Set ι) :
    coordinateRank L Q ≤ Q.ncard := by
  let _ := Fintype.ofFinite Q
  have h := (LinearMap.range (coordinateMap L Q)).finrank_le
  rwa [Module.finrank_pi, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at h

/-- The consistency rank at any partition is at most the input code's
codimension. Apply this to the read-restricted code to discard unused parities. -/
theorem syndromeRank_le_codim [Finite ι] [FiniteDimensional F V]
    (L : V →ₗ[F] (ι → F)) (P : Set ι) :
    syndromeRank L P ≤ Nat.card ι - finrank F (LinearMap.range L) := by
  have hp := coordinateRank_le_ncard L P
  have hf := coordinateRank_le_ncard L Pᶜ
  have hc := ncard_add_ncard_compl P
  dsimp [syndromeRank]
  lia

/-- Deleting unused coordinates cannot increase the redundancy of a linear
input code. This bounds read redundancy by the number of supplied extra forms. -/
theorem ncard_sub_coordinateRank_le_codim [Finite ι] [FiniteDimensional F V]
    (L : V →ₗ[F] (ι → F)) (Q : Set ι) :
    Q.ncard - coordinateRank L Q ≤ Nat.card ι - finrank F (LinearMap.range L) := by
  have hr := syndromeRank_add L Q
  have hc := coordinateRank_le_ncard L Qᶜ
  have hn := ncard_add_ncard_compl Q
  lia

end LinearBoundary

/-- Redundant physical inputs among the linear forms actually read. -/
noncomputable def Network.readRedundancy {J E : Type*} (N : Network F ι J E)
    (L : V →ₗ[F] (ι → F)) : ℕ :=
  N.read.ncard - LinearBoundary.coordinateRank L N.read

section Circuit

variable {σ : Signature} {n : ℕ}
  (I : Interpretation σ F) (Acc : Set F) (c : Circuit σ n 1)
  (L : V →ₗ[F] (Fin n → F)) {S : Set V} {K : ℕ}

/-- A promised circuit reads almost the full independent dimension, even when
arbitrarily many linear inputs are supplied for free. -/
theorem pow_sub_read_rank_lt_of_linear_inputs [FiniteDimensional F V]
    (hS : SumsetFree S K) (hK : K ≤ S.ncard)
    (hc : ∀ x, c.eval I (L x) 0 ∈ Acc ↔ x ∈ S) :
    Nat.card F ^ (finrank F V -
      LinearBoundary.coordinateRank L (constraintNetwork I Acc c).read) < K := by
  apply (constraintNetwork I Acc c).pow_sub_read_rank_lt L hS hK
  intro x
  rw [Compiler.accepted_network]
  change (∀ o : Fin 1, c.eval I (L x) o ∈ Acc) ↔ x ∈ S
  rw [← hc x]
  exact ⟨fun h => h 0, fun h o => Subsingleton.elim o 0 ▸ h⟩

/-- Circuit cycle rank plus independent read rank plus read redundancy is at
most `(fanin - 1) * size + 1`. The redundancy is not silently discarded. -/
theorem cycleRank_add_read_rank_add_redundancy_le {r : ℕ} (hfan : c.FanInAtMost r) :
    (constraintNetwork I Acc c).cycleRank +
      LinearBoundary.coordinateRank L (constraintNetwork I Acc c).read +
      ((constraintNetwork I Acc c).read.ncard -
        LinearBoundary.coordinateRank L (constraintNetwork I Acc c).read) ≤
      (r - 1) * c.innerSize + 1 := by
  have hr := LinearBoundary.coordinateRank_le_ncard L (constraintNetwork I Acc c).read
  have h := Compiler.cycleRank_add_ncard_read_le (out := c.outputs) I (fun _ => Acc) hfan
    (Compiler.connected I _)
  change (constraintNetwork I Acc c).cycleRank + (constraintNetwork I Acc c).read.ncard ≤
    (r - 1) * c.innerSize + 1 at h
  lia

end Circuit

end Frontier
