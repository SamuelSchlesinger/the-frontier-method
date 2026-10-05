/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Ledger.Sweep
public import Frontier.Ledger.Count
public import Frontier.Ledger.Aggregate
public import Frontier.Components
public import Frontier.LowerBound
import Mathlib.Tactic.Ring

/-!
# The lower bound with a ledger

**Main theorem** (`Frontier.lowerBound_ledger`). Fix `r ≥ 2` and assume the layout hypothesis
`LayoutBound (r + 1) A`. Let `S_n ⊆ U^n` be dense `K_n`-rectangle-free sets with
`log K_n = o(n)`, as in `Frontier.lowerBound`, and let `β(n) = o(n)`. For every `ε > 0` and all
large `n`, every circuit deciding `S_n` whose gates have fan-in at most `r`, except for special
gates of any fan-in that have a ledger in a monoid `M` with `log |M| ≤ β(n)`, has
`(r - 1) s > (1 + 1/A - ε) n` for its size `s`.

So the coefficient of the frontier method survives a sublinear amount of unbounded fan-in. For
instance, `k` gates computing AND, OR, parity, or counts modulo `m` of any number of arguments
have a ledger with `log |M| = O(k)` (`Frontier.exists_ledger_of_aggregates`), so `k = o(n)` such
gates are allowed.

**Proof.** Erase the special gates and lay out the network of the erased program, one connected
component after another (`Frontier.LayoutBound.exists_layout_componentwise`). Sweep the circuit
along this layout with the ledger in the messages (`Frontier.Ledger.sweep`). At each step the
transitions are bounded both by the width of the frontier and by the number of inputs of the
component being processed. The frontier counting lemma then finds a component `W` that reads
almost all `n` inputs and whose layout is wide, up to `2 log |M|` and the usual error terms
(`Frontier.Ledger.exists_ncard_le`). The cycle rank of `W` is at most `(r - 1) s + 1` minus the
number of inputs it reads (`Frontier.Compiler.cycleRankOn_add_ncard_readIn_le`), so `W` alone
has the demand and the supply of a connected graph, and the comparison of demand and supply
finishes the proof.
-/

@[expose] public section

namespace Frontier

open Cslib.Circuits Set Filter Asymptotics

universe u v

namespace Ledger

variable {U : Type u} {σ : Signature.{v}} {n : ℕ} {c : Circuit σ n 1} {I : Interpretation σ U}
  {special : ℕ → Prop} {M : Type*} [CommMonoid M] (L : Ledger c.program I special M)

/-- **Counting along a componentwise layout.** If the vertex processed at each step lies in a
closed set containing both frontiers of the step, then some step `t` bounds the size of the set
decided by the circuit by `(K - 1)^2 |V| |M|^3 q^m`, where `m` is the smaller of the width of the
step and the number of inputs read in its closed set. -/
theorem exists_ncard_le [Finite U] [Nonempty U] [Finite M] {Acc : Set U} {K : ℕ}
    (hfree : RectangleFree {x | c.program.trace I x (c.outputs 0) ∈ Acc} K)
    (hK : K ≤ {x | c.program.trace I x (c.outputs 0) ∈ Acc}.ncard)
    (π : Layout (Vtx c special)) (W : ∀ t, t < Nat.card (Vtx c special) → Set (Vtx c special))
    (hW : ∀ t ht, (L.fnet 1).cut (W t ht) = ∅) (hv : ∀ t ht, π.symm ⟨t, ht⟩ ∈ W t ht)
    (hC : ∀ t ht, (L.fnet 1).cut (π.initial t) ∪ (L.fnet 1).cut (π.initial (t + 1)) ⊆
      (L.fnet 1).touching (W t ht)) :
    ∃ t, ∃ ht : t < Nat.card (Vtx c special),
      {x | c.program.trace I x (c.outputs 0) ∈ Acc}.ncard ≤
        (K - 1) ^ 2 * Nat.card (Vtx c special) * Nat.card M ^ 3 *
          Nat.card U ^ min (((L.fnet 1).cut (π.initial t) ∪
            (L.fnet 1).cut (π.initial (t + 1))).ncard +
              ((L.fnet 1).readAt (π.symm ⟨t, ht⟩)).ncard) ((L.fnet 1).readIn (W t ht)).ncard := by
  classical
  set S := {x | c.program.trace I x (c.outputs 0) ∈ Acc}
  have hq : 1 ≤ Nat.card U := Nat.card_pos
  have hsweep : S.ncard ≤ (K - 1) ^ 2 *
      ∑ t ∈ Finset.range (Nat.card (Vtx c special)), ((L.sweep Acc π).transition t '' S).ncard :=
    (L.sweep Acc π).ncard_le hfree hK
  -- The exponent at each step: the smaller of its width and the inputs of its closed set.
  let f : ℕ → ℕ := fun t => if ht : t < Nat.card (Vtx c special) then
    min (((L.fnet 1).cut (π.initial t) ∪ (L.fnet 1).cut (π.initial (t + 1))).ncard +
      ((L.fnet 1).readAt (π.symm ⟨t, ht⟩)).ncard) ((L.fnet 1).readIn (W t ht)).ncard else 0
  have hNpos : 0 < Nat.card (Vtx c special) := by
    by_contra h0
    have : Nat.card (Vtx c special) = 0 := by omega
    rw [this, Finset.range_zero, Finset.sum_empty, mul_zero] at hsweep
    have := hfree.pos
    omega
  obtain ⟨t, htmem, hmax⟩ := Finset.exists_max_image (Finset.range (Nat.card (Vtx c special))) f
    ⟨0, Finset.mem_range.mpr hNpos⟩
  have ht : t < Nat.card (Vtx c special) := Finset.mem_range.mp htmem
  refine ⟨t, ht, ?_⟩
  have hstep : ∀ t' ∈ Finset.range (Nat.card (Vtx c special)),
      ((L.sweep Acc π).transition t' '' S).ncard ≤ Nat.card M ^ 3 * Nat.card U ^ f t := by
    intro t' ht'mem
    have ht' := Finset.mem_range.mp ht'mem
    have h1 := L.ncard_transition_le_width (Acc := Acc) π ht'
    have h2 := L.ncard_transition_le_closed (Acc := Acc) π ht' (hW t' ht') (hv t' ht')
      (hC t' ht')
    calc ((L.sweep Acc π).transition t' '' S).ncard ≤ Nat.card M ^ 3 * Nat.card U ^ f t' := by
          simp only [f, ht', dite_true]
          rcases min_cases (((L.fnet 1).cut (π.initial t') ∪
              (L.fnet 1).cut (π.initial (t' + 1))).ncard +
              ((L.fnet 1).readAt (π.symm ⟨t', ht'⟩)).ncard)
            ((L.fnet 1).readIn (W t' ht')).ncard with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
          · exact h1
          · exact h2
      _ ≤ Nat.card M ^ 3 * Nat.card U ^ f t :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hq (hmax t' ht'mem))
  have hft : f t = min (((L.fnet 1).cut (π.initial t) ∪
      (L.fnet 1).cut (π.initial (t + 1))).ncard + ((L.fnet 1).readAt (π.symm ⟨t, ht⟩)).ncard)
      ((L.fnet 1).readIn (W t ht)).ncard := by
    simp only [f, ht, dite_true]
  calc S.ncard ≤ (K - 1) ^ 2 * ∑ t ∈ Finset.range (Nat.card (Vtx c special)),
        ((L.sweep Acc π).transition t '' S).ncard := hsweep
    _ ≤ (K - 1) ^ 2 * (Nat.card (Vtx c special) * (Nat.card M ^ 3 * Nat.card U ^ f t)) := by
        gcongr
        simpa using Finset.sum_le_card_nsmul (Finset.range (Nat.card (Vtx c special))) _ _ hstep
    _ = _ := by rw [← hft]; ring

end Ledger

variable {U : Type u} [Finite U] [Nontrivial U]

/-- **The frontier lower bound with a ledger.** Let `r ≥ 2` and assume the layout hypothesis for
maximum degree `r + 1` with coefficient `A > 0`. Let `S_n ⊆ U^n` be dense `K_n`-rectangle-free
sets with `log K_n = o(n)`, and let `β(n) = o(n)`. Then for every `ε > 0` and all large `n`, every
circuit deciding `S_n`, over any basis on `U`, whose gates have fan-in at most `r` except for
special gates of any fan-in with a ledger in a monoid `M` with `log |M| ≤ β(n)`, has size `s`
with `(r - 1) s > (1 + 1/A - ε) n`. -/
theorem lowerBound_ledger {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : ℕ → Prop) (M : Type) [CommMonoid M] [Finite M],
        (∀ g : Fin c.size, ¬ special g → σ.Arity (c.program.lines g).op ≤ r) →
        Ledger c.program I special M → Real.log (Nat.card M) ≤ β n →
        Decides c I Acc (S n) → (1 + 1 / A - ε) * n < (r - 1) * c.size := by
  set q := Nat.card U
  have hq : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  have hL : 0 < Real.log q := Real.log_pos hq
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL2 : Real.log 2 ≤ Real.log q :=
    Real.log_le_log two_pos (by exact_mod_cast Finite.one_lt_card)
  -- The constant bounding the size of the graph and the base change of its logarithm.
  set κ : ℝ := 7 + 1 / Real.log 2
  have hκ : 0 ≤ κ := by positivity
  have hκ7 : 7 ≤ κ := by simp only [κ]; linarith [show 0 ≤ 1 / Real.log 2 by positivity]
  -- The error of the problem: the density defect, the threshold, the ledger, and constants.
  set e : ℕ → ℝ := fun n => (n - Real.logb q (S n).ncard) + 2 * Real.logb q (K n) +
    3 * (β n / Real.log 2) + (r + 3)
  have he : e =o[atTop] fun n => (n : ℝ) := by
    have h1 := isLittleO_sub_logb_ncard S hdense
    have h2 : (fun n : ℕ => 2 * Real.logb q (K n)) =o[atTop] fun n => (n : ℝ) :=
      (hK.const_mul_left (2 / Real.log q)).congr_left fun n => by
        simp only [Real.logb]; ring
    have h3 : (fun n : ℕ => 3 * (β n / Real.log 2)) =o[atTop] fun n => (n : ℝ) :=
      (hβ.const_mul_left (3 / Real.log 2)).congr_left fun n => by ring
    have h4 : (fun _ : ℕ => ((r : ℝ) + 3)) =o[atTop] fun n => (n : ℝ) :=
      isLittleO_const_left.mpr (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop))
    exact ((h1.add h2).add h3).add h4
  obtain ⟨η, hη, H⟩ := eventually_lt_of_demand hA hκ hε
  obtain ⟨C, hC⟩ := hlayout.exists_layout_componentwise hη
  filter_upwards [H C e he, hfree, eventually_card_mul_sq_le_ncard S K hfree hK hdense] with
    n hn hfreen hbign
  intro σ I Acc c special M _ _ hfan L hM hS
  -- The set decided by the circuit.
  have hSeq : S n = {x | c.program.trace I x (c.outputs 0) ∈ Acc} := by
    ext x; exact hS x
  have hK1 := hfreen.pos
  rw [hSeq] at hfreen hbign
  have hKS : K n ≤ {x | c.program.trace I x (c.outputs 0) ∈ Acc}.ncard :=
    le_trans (Nat.le_mul_of_pos_left _ Nat.card_pos) ((Nat.mul_le_mul_left _
      (Nat.le_self_pow two_ne_zero _)).trans hbign)
  -- Lay out the network of the erased program one component after another.
  set V := Nat.card (Ledger.Vtx c special)
  have hfan' := fanInAtMost_erase special c.program hfan
  obtain ⟨π, hπ⟩ := hC _ _ (L.fnet 1).toMultigraph (Compiler.loopless _ _)
    (Compiler.maxDegreeLE _ _ hr hfan')
  choose W hvW hWc hWn hF₀ hF₁ hb₀ _ using hπ
  obtain ⟨t, ht, hcount⟩ := L.exists_ncard_le hfreen hKS π W hWc hvW
    fun t ht => union_subset (hF₀ t ht) (hF₁ t ht)
  -- The quantities of the comparison.
  set B := (A + η) * (L.fnet 1).cycleRankOn (W t ht) + η * V + C
  set a := ((L.fnet 1).cut (π.initial t) ∪ (L.fnet 1).cut (π.initial (t + 1))).ncard +
    ((L.fnet 1).readAt (π.symm ⟨t, ht⟩)).ncard
  set nW := ((L.fnet 1).readIn (W t ht)).ncard
  set s : ℝ := (((r - 1) * c.size : ℕ) : ℝ)
  have hs : s = (r - 1) * c.size := by
    simp only [s]; rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
  -- The width of the step is at most the frontier and the edges of the vertex processed.
  have ha : (a : ℝ) ≤ B + (r + 2) := by
    have hnext : (L.fnet 1).cut (π.initial (t + 1)) ⊆
        (L.fnet 1).cut (π.initial t) ∪ (L.fnet 1).edgesAt (π.symm ⟨t, ht⟩) := by
      rw [π.initial_succ ht]
      exact Multigraph.cut_insert_subset _ _ _
    have hU : ((L.fnet 1).cut (π.initial t) ∪ (L.fnet 1).cut (π.initial (t + 1))).ncard ≤
        ((L.fnet 1).cut (π.initial t)).ncard + (r + 1) :=
      (ncard_le_ncard (union_subset subset_union_left hnext) (toFinite _)).trans
        ((ncard_union_le _ _).trans (Nat.add_le_add_left
          (Compiler.maxDegreeLE _ _ hr hfan' _) _))
    have hR : ((L.fnet 1).readAt (π.symm ⟨t, ht⟩)).ncard ≤ 1 :=
      Compiler.ncard_readAt_le _ _ _
    have : a ≤ ((L.fnet 1).cut (π.initial t)).ncard + (r + 2) := by simp only [a]; omega
    have hF := hb₀ t ht
    have : (a : ℝ) ≤ ((L.fnet 1).cut (π.initial t)).ncard + (r + 2) := by exact_mod_cast this
    linarith
  -- The cycle rank of the component and the inputs it reads.
  have hρ : ((L.fnet 1).cycleRankOn (W t ht) : ℝ) + nW ≤ s + 1 := by
    have h := Compiler.cycleRankOn_add_ncard_readIn_le _ _ hfan' (hWc t ht) (hWn t ht)
    have hinner : (erase special c.program).innerGates.card ≤ c.size :=
      (Finset.card_le_univ _).trans (by simp)
    have : (L.fnet 1).cycleRankOn (W t ht) + nW ≤ (r - 1) * c.size + 1 :=
      h.trans (by gcongr)
    simp only [s]
    exact_mod_cast this
  -- The size of the graph.
  have hV : (V : ℝ) ≤ κ * (n + s + 1) := by
    have h := Compiler.card_vertex_le (p := erase special c.program) (out := Ledger.outs c) hfan'
    have hinner : (erase special c.program).innerGates.card ≤ c.size :=
      (Finset.card_le_univ _).trans (by simp)
    have hO : Nat.card (Option (Wire n c.size)) = n + c.size + 1 := by
      rw [Finite.card_option, Nat.card_eq_fintype_card, Wire.card]
    have : V ≤ 7 * ((r - 1) * c.size) + 3 * n + 3 := by
      have h7 : 2 * r + 3 ≤ 7 * (r - 1) := by omega
      have := Nat.mul_le_mul_left (2 * r) hinner
      have := Nat.mul_le_mul_right c.size h7
      simp only [V]
      rw [hO] at h
      nlinarith
    have hV7 : (V : ℝ) ≤ 7 * s + 3 * n + 3 := by simp only [s]; exact_mod_cast this
    have hns : 0 ≤ (n : ℝ) + s + 1 := by positivity
    nlinarith
  -- Take logarithms in the counting bound.
  have hVpos : 0 < V := lt_of_le_of_lt (Nat.zero_le _) ht
  have hMpos : 0 < Nat.card M := Nat.card_pos
  have hcount' : ({x | c.program.trace I x (c.outputs 0) ∈ Acc}.ncard : ℝ) ≤
      (K n : ℝ) ^ 2 * V * (Nat.card M : ℝ) ^ 3 * (q : ℝ) ^ (min a nW) := by
    have : (K n - 1) ^ 2 ≤ K n ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
    have h := hcount.trans (by gcongr : (K n - 1) ^ 2 * V * Nat.card M ^ 3 * q ^ min a nW ≤
      K n ^ 2 * V * Nat.card M ^ 3 * q ^ min a nW)
    exact_mod_cast h
  have hSpos : (0 : ℝ) < {x | c.program.trace I x (c.outputs 0) ∈ Acc}.ncard := by
    have : 0 < {x | c.program.trace I x (c.outputs 0) ∈ Acc}.ncard := lt_of_lt_of_le hK1 hKS
    exact_mod_cast this
  have hlogS : Real.logb q {x | c.program.trace I x (c.outputs 0) ∈ Acc}.ncard ≤
      2 * Real.logb q (K n) + Real.logb q V + 3 * Real.logb q (Nat.card M) + min a nW := by
    have hK0 : (0 : ℝ) < K n := by exact_mod_cast hK1
    have hV0 : (0 : ℝ) < V := by exact_mod_cast hVpos
    have hM0 : (0 : ℝ) < Nat.card M := by exact_mod_cast hMpos
    calc _ ≤ Real.logb q ((K n : ℝ) ^ 2 * V * (Nat.card M : ℝ) ^ 3 * (q : ℝ) ^ (min a nW)) :=
          Real.logb_le_logb_of_le hq hSpos hcount'
      _ = _ := by
          rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
            (by positivity), Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
            Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hq]
          push_cast
          ring
  rw [← hSeq] at hlogS
  -- Bound the logarithms of the graph and of the ledger.
  have hlogV : Real.logb q V ≤ κ * Real.log (V + 1) := by
    have hV0 : (1 : ℝ) ≤ V := by exact_mod_cast hVpos
    have h0 : 0 ≤ Real.log V := Real.log_nonneg hV0
    have h1 : Real.log V ≤ Real.log (V + 1) := Real.log_le_log (by linarith) (by linarith)
    calc Real.logb q V ≤ Real.log V / Real.log 2 := div_le_div_of_nonneg_left h0 h2 hL2
      _ ≤ Real.log (V + 1) / Real.log 2 := by gcongr
      _ ≤ κ * Real.log (V + 1) := by
          rw [div_eq_mul_one_div, mul_comm]
          exact mul_le_mul_of_nonneg_right (by simp [κ]) (h0.trans h1)
  have hlogM : Real.logb q (Nat.card M) ≤ β n / Real.log 2 := by
    have h0 : 0 ≤ Real.log (Nat.card M) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hMpos.ne')
    exact (div_le_div_of_nonneg_left h0 h2 hL2).trans (div_le_div_of_nonneg_right hM h2.le)
  have hlogK : 0 ≤ Real.logb q (K n) := Real.logb_nonneg hq (by exact_mod_cast hK1)
  have hmin1 : ((min a nW : ℕ) : ℝ) ≤ a := by exact_mod_cast min_le_left a nW
  have hmin2 : ((min a nW : ℕ) : ℝ) ≤ nW := by exact_mod_cast min_le_right a nW
  have hlog0 : 0 ≤ Real.log (V + 1) := Real.log_nonneg (by
    have : (0 : ℝ) ≤ V := Nat.cast_nonneg _
    linarith)
  rw [← hs]
  refine hn s V B (Nat.cast_nonneg _) (Nat.cast_nonneg _) hV ?_ ?_
  · -- The demand: the component is wide.
    simp only [e]
    linarith
  · -- The supply: the component reads almost all inputs, so its cycle rank is small.
    have hρ' : ((L.fnet 1).cycleRankOn (W t ht) : ℝ) ≤ s - n + e n + κ * Real.log (V + 1) := by
      simp only [e]
      linarith
    have := mul_le_mul_of_nonneg_left hρ' (by linarith : 0 ≤ A + η)
    simp only [B]
    linarith

/-- **Aggregate gates.** Under the hypotheses of `Frontier.lowerBound`, let `β(n) = o(n)`. For
every `ε > 0` and all large `n`, every circuit deciding `S_n` whose gates have fan-in at most `r`,
except for `k` special gates of any fan-in that aggregate in a finite commutative monoid `T`,
with `k log |T| ≤ β(n)`, has size `s` with `(r - 1) s > (1 + 1/A - ε) n`. For instance, the
special gates may compute AND, OR, parity, or counts modulo `m` of any number of arguments. -/
theorem lowerBound_aggregate {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ))
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : ℕ → Prop) (T : Type) [CommMonoid T] [Finite T],
        (∀ g : Fin c.size, ¬ special g → σ.Arity (c.program.lines g).op ≤ r) →
        (∀ g : Fin c.size, special g → Aggregates (I (c.program.lines g).op) T) →
        Nat.card {g : Fin c.size // special g} * Real.log (Nat.card T) ≤ β n →
        Decides c I Acc (S n) → (1 + 1 / A - ε) * n < (r - 1) * c.size := by
  filter_upwards [lowerBound_ledger hr hA hlayout S K hfree hK hdense hβ hε] with n hn
  intro σ I Acc c special T _ _ hfan hagg hk hS
  obtain ⟨L⟩ := exists_ledger_of_aggregates c.program I special T hagg
  refine hn σ I Acc c special _ hfan L ?_ hS
  rw [Nat.card_fun, Nat.cast_pow, Real.log_pow]
  exact hk

end Frontier
