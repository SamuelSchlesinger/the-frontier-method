/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Compiler
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# From small circuits to wide graphs

This file combines the three ingredients of the frontier method for a single input length:

* compiling a circuit into a constraint network (`Frontier.Compiler`),
* the frontier counting lemma for networks (`Frontier.Network.ncard_accepted_le`), and
* the support lemma for rectangle-free sets (`Frontier.RectangleFree.pow_ncard_compl_lt`).

**The reduction theorem** (`Frontier.exists_graph_of_decides`). Let `c` be a circuit with `s`
gates of fan-in at most `r ≥ 2`, over any basis on a finite alphabet `U` with `q ≥ 2` symbols,
that decides a `K`-rectangle-free set `S ⊆ U^n` with `|S| ≥ q K^2`. Then there is a connected,
loopless multigraph `G` of maximum degree `r + 1` with at most `n + (r + 1) s + 2` vertices and
cycle rank

`β₁(G) ≤ (r - 1) s - n + log_q K + 1`,

every layout of which has width at least

`log_q |S| - 3 log_q K - log_q (|V(G)| + 1) - (r + 2)`.

For fan-in two the graph is subcubic, `β₁(G) ≤ s - n + log_q K + 1`, and the width is at least
`log_q |S| - 3 log_q K - log_q (|V(G)| + 1) - 4`.

The graph is the constraint graph of `c`. The cycle rank bound is the count of the compiler,
together with the support lemma, which says that `c` reads all but `log_q K` of its inputs.
The width bound is the frontier counting lemma, in which the unread inputs contribute at most
`K` transitions, again by the support lemma.

For a dense set, `log_q |S| ≈ n`; so a small circuit gives a graph whose cycle rank is about
`(r - 1) s - n` but whose layouts all have width about `n`.
-/

@[expose] public section

namespace Frontier

open Cslib.Circuits Set

variable {U : Type*} {σ : Signature} {n : ℕ}

/-- A circuit with one output *decides* a set of inputs `S`, accepting the values in `Acc`,
when an input lies in `S` exactly if the output of the circuit lies in `Acc`. -/
def Decides (c : Circuit σ n 1) (I : Interpretation σ U) (Acc : Set U)
    (S : Set (Fin n → U)) : Prop :=
  ∀ x, x ∈ S ↔ c.eval I x 0 ∈ Acc

/-- A circuit computing a Boolean function decides the set of inputs it maps to `true`. -/
theorem Decides.of_computes {c : Circuit σ n 1} {I : Interpretation σ Bool}
    {f : (Fin n → Bool) → Bool} (h : c.Computes I (single f)) :
    Decides c I {true} {x | f x = true} := fun x => by
  have h0 := congrFun (h x) 0
  rw [single_apply] at h0
  simp [h0]

/-- A rectangle-free set has a positive threshold. -/
theorem RectangleFree.pos {ι : Type*} {S : Set (ι → U)} {K : ℕ} (h : RectangleFree S K) :
    0 < K := by
  rcases h univ ∅ ∅ (by simp [rectangle]) with h | h <;> simpa using h

/-- The constraint network of a one-output circuit. -/
noncomputable abbrev constraintNetwork (I : Interpretation σ U) (Acc : Set U)
    (c : Circuit σ n 1) :=
  Compiler.network c.program (c.outputs 0) I Acc

theorem accepted_constraintNetwork {I : Interpretation σ U} {Acc : Set U} {c : Circuit σ n 1}
    {S : Set (Fin n → U)} (hS : Decides c I Acc S) : (constraintNetwork I Acc c).accepted = S := by
  rw [Compiler.accepted_network]
  ext x
  exact (hS x).symm

section Reduction

variable [Finite U] [Nontrivial U] {I : Interpretation σ U} {Acc : Set U} {c : Circuit σ n 1}
  {S : Set (Fin n → U)} {K r : ℕ}

/-- **The support lemma, for circuits.** A circuit deciding a large rectangle-free set reads all
but fewer than `log_q K` of its inputs. -/
theorem pow_ncard_unread_lt (hS : Decides c I Acc S) (hfree : RectangleFree S K)
    (hbig : Nat.card U * K ^ 2 ≤ S.ncard) :
    Nat.card U ^ (constraintNetwork I Acc c).readᶜ.ncard < K := by
  rw [← accepted_constraintNetwork hS] at hfree hbig
  exact hfree.pow_ncard_compl_lt (constraintNetwork I Acc c).dependsOn_read hbig

/-- **The cycle rank of the constraint graph** is at most `(r - 1) s - n + log_q K + 1` for
fan-in at most `r`. -/
theorem cycleRank_le (hfan : c.FanInAtMost r) (hS : Decides c I Acc S)
    (hfree : RectangleFree S K) (hbig : Nat.card U * K ^ 2 ≤ S.ncard) :
    ((constraintNetwork I Acc c).cycleRank : ℝ) ≤
      ((r - 1) * c.size : ℕ) - n + Real.logb (Nat.card U) K + 1 := by
  set N := constraintNetwork I Acc c
  have hq : (1 : ℝ) < Nat.card U := by exact_mod_cast Finite.one_lt_card
  have hrank := Compiler.cycleRank_add_ncard_read_le (out := c.outputs 0) I Acc hfan
  have hunread : (N.readᶜ.ncard : ℝ) < Real.logb (Nat.card U) K := by
    rw [Real.lt_logb_iff_rpow_lt hq (by exact_mod_cast hfree.pos), Real.rpow_natCast]
    exact_mod_cast pow_ncard_unread_lt hS hfree hbig
  have hcompl : N.readᶜ.ncard + N.read.ncard = n := by
    rw [ncard_compl N.read, Nat.card_eq_fintype_card, Fintype.card_fin]
    have := ncard_le_card N.read
    rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  have : (N.cycleRank : ℝ) + N.read.ncard ≤ ((r - 1) * c.size : ℕ) + 1 := by
    exact_mod_cast hrank
  have : (N.readᶜ.ncard : ℝ) + N.read.ncard = n := by exact_mod_cast hcompl
  linarith

/-- **Every layout of the constraint graph is wide.** For fan-in at most `r ≥ 2`, if all
frontiers of a layout have at most `w` edges, then
`log_q |S| ≤ w + (r + 2) + 3 log_q K + log_q (|V| + 1)`. -/
theorem logb_ncard_le (hr : 2 ≤ r) (hfan : c.FanInAtMost r) (hS : Decides c I Acc S)
    (hfree : RectangleFree S K) (hbig : Nat.card U * K ^ 2 ≤ S.ncard)
    (π : Layout (Compiler.Vertex c.program (c.outputs 0))) {w : ℕ}
    (hw : ∀ t, ((constraintNetwork I Acc c).cut (π.initial t)).ncard ≤ w) :
    Real.logb (Nat.card U) S.ncard ≤
      w + (r + 2) + 3 * Real.logb (Nat.card U) K +
        Real.logb (Nat.card U) (Nat.card (Compiler.Vertex c.program (c.outputs 0)) + 1) := by
  set N := constraintNetwork I Acc c
  set q := Nat.card U
  set V := Nat.card (Compiler.Vertex c.program (c.outputs 0))
  have hq1 : 1 < q := Finite.one_lt_card
  have hK := hfree.pos
  have hacc := accepted_constraintNetwork hS
  -- The frontier counting lemma, with degree `r + 1` and one input per vertex.
  have hcount := N.ncard_accepted_le π (hacc ▸ hfree)
    (hacc ▸ (Nat.le_mul_of_pos_left K (by positivity)).trans
      ((Nat.mul_le_mul_left _ (Nat.le_self_pow two_ne_zero K)).trans hbig))
    hw (Compiler.maxDegreeLE I Acc hr hfan) (Compiler.ncard_readAt_le I Acc)
  rw [hacc] at hcount
  -- The unread inputs carry fewer than `K` assignments.
  have hunread := pow_ncard_unread_lt hS hfree hbig
  rw [show w + (r + 1) + 1 = w + (r + 2) by ring] at hcount
  have hnat : S.ncard ≤ K ^ 3 * (V + 1) * q ^ (w + (r + 2)) := by
    calc S.ncard ≤ (K - 1) ^ 2 * (V * q ^ (w + (r + 2)) + q ^ N.readᶜ.ncard) := hcount
      _ ≤ K ^ 2 * (V * K * q ^ (w + (r + 2)) + K * q ^ (w + (r + 2))) := by
          gcongr
          · omega
          · exact Nat.le_mul_of_pos_right _ hK
          · exact hunread.le.trans (Nat.le_mul_of_pos_right _ (by positivity))
      _ = K ^ 3 * (V + 1) * q ^ (w + (r + 2)) := by ring
  have hSpos : (0 : ℝ) < S.ncard := by
    have : 0 < S.ncard := lt_of_lt_of_le (by positivity) hbig
    exact_mod_cast this
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq1
  calc Real.logb q S.ncard
      ≤ Real.logb q ((K : ℝ) ^ 3 * (V + 1) * (q : ℝ) ^ (w + (r + 2))) :=
        Real.logb_le_logb_of_le hqR hSpos (by exact_mod_cast hnat)
    _ = w + (r + 2) + 3 * Real.logb q K + Real.logb q (V + 1) := by
        have hKR : (0 : ℝ) < K := by exact_mod_cast hK
        rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
          (by positivity), Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hqR]
        push_cast
        ring

/-- **The reduction theorem.** A circuit of size `s` with fan-in at most `r ≥ 2`, over any basis
on `U`, deciding a `K`-rectangle-free set `S ⊆ U^n` with `|S| ≥ q K^2`, yields a connected,
loopless multigraph of maximum degree `r + 1` with at most `n + (r + 1) s + 2` vertices and
cycle rank at most `(r - 1) s - n + log_q K + 1`, every layout of which has width at least
`log_q |S| - 3 log_q K - log_q (|V| + 1) - (r + 2)`. -/
theorem exists_graph_of_decides (hr : 2 ≤ r) (hfan : c.FanInAtMost r) (hS : Decides c I Acc S)
    (hfree : RectangleFree S K) (hbig : Nat.card U * K ^ 2 ≤ S.ncard) :
    ∃ (V E : Type) (_ : Finite V) (_ : Finite E) (G : Multigraph V E),
      G.Connected ∧ G.Loopless ∧ G.MaxDegreeLE (r + 1) ∧
      Nat.card V ≤ n + (r + 1) * c.size + 2 ∧
      (G.cycleRank : ℝ) ≤ ((r - 1) * c.size : ℕ) - n + Real.logb (Nat.card U) K + 1 ∧
      ∀ (π : Layout V) (w : ℕ), (∀ t, (G.cut (π.initial t)).ncard ≤ w) →
        Real.logb (Nat.card U) S.ncard ≤
          w + (r + 2) + 3 * Real.logb (Nat.card U) K +
            Real.logb (Nat.card U) (Nat.card V + 1) :=
  ⟨_, _, inferInstance, inferInstance, (constraintNetwork I Acc c).toMultigraph,
    Compiler.connected I Acc, Compiler.loopless I Acc, Compiler.maxDegreeLE I Acc hr hfan,
    Compiler.card_vertex_le hfan, cycleRank_le hfan hS hfree hbig,
    fun π _ hw => logb_ncard_le hr hfan hS hfree hbig π hw⟩

end Reduction

end Frontier
