/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Rectangle
public import Frontier.ForMathlib.SetCard
public import Mathlib.Order.Lattice.Nat
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Sweeps and the frontier counting lemma

A *sweep* of a set of inputs `S ⊆ U^ι` reveals the coordinates of an input a few at a time:
`∅ = X 0, X 1, ..., X T = ι`. At each time `t` an input has a *message* `μ t x`, which may
depend on the whole input. The defining property is that messages permit splicing:
if two inputs of `S` have the same message at time `t`, then
the revealed part of one may be spliced onto the unrevealed part of the other without leaving
`S`. The last message, sent once everything is revealed, carries no information.

Between times `t` and `t + 1` an input `x` takes the *transition*
`(μ t x, μ (t + 1) x, x|_{X (t + 1) \ X t})`: the message before the step, the message after
it, and the coordinates revealed during it.

**The frontier counting lemma** (`Sweep.ncard_le`). If `S` is `K`-rectangle-free and has at
least `K` elements, then
`|S| ≤ (K - 1) ^ 2 · ∑_t #{transitions taken at step t}`.

The proof charges each input `x` to the first time `t + 1` at which the inputs sharing its
message have at least `K` distinct revealed parts. Their rectangular hull lies inside `S`, so
they have fewer than `K` distinct unrevealed parts. At time `t` the inputs sharing the message
of `x` still had fewer than `K` distinct revealed parts. An input charged to a step is
determined by its transition, its part revealed by time `t`, and its part unrevealed at time
`t + 1`; hence at most `(K - 1) ^ 2` inputs share a charged step and a transition.

Nothing here mentions graphs or circuits: a sweep is an abstract family of splicing messages.
Its transitions alone need not form a correct branching program.
Constraint networks swept along a vertex ordering produce sweeps whose messages are the values
on the edges of the frontier (`Frontier.Network.sweep`).

## Main definitions

* `Frontier.Sweep S M`: a sweep of `S` with messages in `M`.
* `Frontier.Sweep.transition`: the transition taken by an input at a step.

## Main results

* `Frontier.Sweep.ncard_le`: the frontier counting lemma.
-/

@[expose] public section

namespace Frontier

open Set

variable {ι U M : Type*}

/-- A *sweep* of a set of inputs `S`: coordinates revealed over time, starting from none and
ending with all, and a message at each time such that inputs of `S` sending the same message
can exchange their unrevealed parts. -/
structure Sweep (S : Set (ι → U)) (M : Type*) where
  /-- The number of steps. -/
  length : ℕ
  /-- The coordinates revealed by time `t`. -/
  revealed : ℕ → Set ι
  /-- Nothing is revealed at the start. -/
  revealed_zero : revealed 0 = ∅
  /-- Everything is revealed at the end. -/
  revealed_length : revealed length = univ
  /-- The message at time `t`, possibly depending on the whole input. -/
  message : ℕ → (ι → U) → M
  /-- The final message is the same for all inputs of `S`. -/
  message_length : ∀ x ∈ S, ∀ y ∈ S, message length x = message length y
  /-- Messages are sufficient: two inputs of `S` with the same message at time `t` may be
  spliced, the revealed part of one with the unrevealed part of the other, inside `S`. -/
  splice : ∀ t, ∀ x ∈ S, ∀ y ∈ S, message t x = message t y →
    ∀ z, EqOn z x (revealed t) → EqOn z y (revealed t)ᶜ → z ∈ S

namespace Sweep

variable {S : Set (ι → U)} (P : Sweep S M)

/-- The coordinates revealed during step `t`, between times `t` and `t + 1`. -/
def newly (t : ℕ) : Set ι :=
  P.revealed (t + 1) \ P.revealed t

/-- The transition taken by `x` at step `t`: its messages before and after the step, and its
part revealed during the step. -/
def transition (t : ℕ) (x : ι → U) : M × M × (P.newly t → U) :=
  (P.message t x, P.message (t + 1) x, (P.newly t).domRestrict x)

/-! ### The proof of the counting lemma -/

/-- The inputs of `S` that send the same message as `x` at time `t`. -/
def peers (t : ℕ) (x : ι → U) : Set (ι → U) :=
  {y ∈ S | P.message t y = P.message t x}

/-- The distinct parts revealed by time `t` among the peers of `x`. -/
def pastSide (t : ℕ) (x : ι → U) : Set (P.revealed t → U) :=
  (P.revealed t).domRestrict '' P.peers t x

/-- The distinct parts unrevealed at time `t` among the peers of `x`. -/
def futureSide (t : ℕ) (x : ι → U) : Set (↥(P.revealed t)ᶜ → U) :=
  (P.revealed t)ᶜ.domRestrict '' P.peers t x

/-- The rectangular hull of the peers lies inside `S`: one of its sides is small. -/
theorem pastSide_lt_or_futureSide_lt {K : ℕ} (hS : RectangleFree S K) (t : ℕ) (x : ι → U) :
    (P.pastSide t x).ncard < K ∨ (P.futureSide t x).ncard < K := by
  refine hS _ _ _ fun z ⟨⟨y, ⟨hy, hyx⟩, hzy⟩, ⟨y', ⟨hy', hy'x⟩, hzy'⟩⟩ => ?_
  exact P.splice t y hy y' hy' (hyx.trans hy'x.symm) z
    (domRestrict_eq_domRestrict_iff.mp hzy).symm (domRestrict_eq_domRestrict_iff.mp hzy').symm

/-- At the start nothing is revealed, so there is at most one revealed part. -/
theorem ncard_pastSide_zero_le (x : ι → U) : (P.pastSide 0 x).ncard ≤ 1 := by
  have : Subsingleton (P.revealed 0 → U) :=
    ⟨fun a b => funext fun i => absurd i.2 (by simp [P.revealed_zero])⟩
  exact (ncard_le_one (toFinite _)).mpr fun a _ b _ => Subsingleton.elim a b

/-- At the end everything is revealed and every input of `S` is a peer, so the revealed parts
are as numerous as `S`. -/
theorem ncard_pastSide_length [Finite ι] [Finite U] {x : ι → U} (hx : x ∈ S) :
    (P.pastSide P.length x).ncard = S.ncard := by
  have hpeers : P.peers P.length x = S :=
    subset_antisymm (fun _ hy => hy.1) fun y hy => ⟨hy, P.message_length y hy x hx⟩
  rw [pastSide, hpeers]
  refine ncard_image_of_injective _ fun y y' h => funext fun i => ?_
  exact domRestrict_eq_domRestrict_iff.mp h (by simp [P.revealed_length])

/-- The time at which `x` is charged: the first time its peers have at least `K` distinct
revealed parts. -/
noncomputable def chargeTime (K : ℕ) (x : ι → U) : ℕ :=
  sInf {t | K ≤ (P.pastSide t x).ncard}

/-- The total number of transitions used by accepted inputs. -/
noncomputable def transitionCount : ℕ :=
  ∑ t ∈ Finset.range P.length, (P.transition t '' S).ncard

/-- Inputs whose first threshold crossing occurs at this transition. -/
def chargedInputs (K t : ℕ) : Set (ι → U) :=
  {x ∈ S | P.chargeTime K x = t + 1}

/-- Count only transitions to which at least one input is charged. -/
noncomputable def chargedTransitionCount (K : ℕ) : ℕ :=
  ∑ t ∈ Finset.range P.length, (P.transition t '' P.chargedInputs K t).ncard

theorem chargedTransitionCount_le [Finite ι] [Finite U] (K : ℕ) :
    P.chargedTransitionCount K ≤ P.transitionCount := by
  apply Finset.sum_le_sum
  intro t _
  exact ncard_le_ncard (image_mono fun _ hx => hx.1)

/-- Threshold charging only counts charged transitions, with asymmetric thresholds. -/
theorem ncard_le_charged_of_small_sides [Finite ι] [Finite U] {KL KR : ℕ}
    (hKL : 1 < KL) (hK : KL ≤ S.ncard)
    (hsmall : ∀ t, ∀ x ∈ S, (P.pastSide t x).ncard < KL ∨ (P.futureSide t x).ncard < KR) :
    S.ncard ≤ (KL - 1) * (KR - 1) * P.chargedTransitionCount KL := by
  -- The charge time is well defined, positive, and at most the length of the sweep.
  have hlength : ∀ x ∈ S, P.length ∈ {t | KL ≤ (P.pastSide t x).ncard} := fun x hx =>
    show KL ≤ _ by rw [P.ncard_pastSide_length hx]; exact hK
  have hcharged : ∀ x ∈ S, KL ≤ (P.pastSide (P.chargeTime KL x) x).ncard := fun x hx =>
    Nat.sInf_mem ⟨_, hlength x hx⟩
  have hbefore : ∀ x, ∀ t < P.chargeTime KL x, (P.pastSide t x).ncard < KL := fun x t ht =>
    not_le.mp (Nat.notMem_of_lt_sInf (s := {t | KL ≤ (P.pastSide t x).ncard}) ht)
  have hle_length : ∀ x ∈ S, P.chargeTime KL x ≤ P.length := fun x hx =>
    Nat.sInf_le (hlength x hx)
  have hpos : ∀ x ∈ S, 0 < P.chargeTime KL x := by
    intro x hx
    refine Nat.pos_of_ne_zero fun h0 => ?_
    have h1 := hcharged x hx
    rw [h0] at h1
    have h1 := h1.trans (P.ncard_pastSide_zero_le x)
    lia
  -- Split `S` by the step `t` whose completion charges an input: `chargeTime = t + 1`.
  let step : (ι → U) → ℕ := fun x => P.chargeTime KL x - 1
  have hstep (t : ℕ) : S ∩ step ⁻¹' {t} = P.chargedInputs KL t := by
    ext x
    change (x ∈ S ∧ P.chargeTime KL x - 1 = t) ↔
      x ∈ S ∧ P.chargeTime KL x = t + 1
    constructor
    · rintro ⟨hx, ht⟩
      have := hpos x hx
      exact ⟨hx, by lia⟩
    · rintro ⟨hx, ht⟩
      exact ⟨hx, by lia⟩
  calc S.ncard
      ≤ ∑ t ∈ Finset.range P.length, (S ∩ step ⁻¹' {t}).ncard :=
        ncard_le_sum_ncard_fiber (toFinite S) step P.length fun x hx => by
          have := hle_length x hx; have := hpos x hx; simp only [step]; lia
    _ ≤ ∑ t ∈ Finset.range P.length, ((KL - 1) * (KR - 1)) *
        (P.transition t '' P.chargedInputs KL t).ncard := by
        refine Finset.sum_le_sum fun t _ => ?_
        rw [← hstep t]
        refine ncard_le_mul_ncard_image (toFinite _) (P.transition t) _ fun τ => ?_
        -- The inputs charged at step `t` with transition `τ` are at most `((KL - 1) * (KR - 1))`.
        rcases (S ∩ step ⁻¹' {t} ∩ P.transition t ⁻¹' {τ}).eq_empty_or_nonempty with h | ⟨x, hx⟩
        · simp [h]
        obtain ⟨⟨hxS, hxt⟩, hxτ⟩ := hx
        have hxcharge : P.chargeTime KL x = t + 1 := by
          have := hpos x hxS; simp only [step, mem_preimage, mem_singleton_iff] at hxt; lia
        have hpast : (P.pastSide t x).ncard ≤ KL - 1 := by
          have := hbefore x t (by lia); lia
        have hfuture : (P.futureSide (t + 1) x).ncard ≤ KR - 1 := by
          have := hcharged x hxS
          rw [hxcharge] at this
          rcases hsmall (t + 1) x hxS with h | h <;> lia
        calc (S ∩ step ⁻¹' {t} ∩ P.transition t ⁻¹' {τ}).ncard
            ≤ (P.pastSide t x ×ˢ P.futureSide (t + 1) x).ncard := by
              refine ncard_le_ncard_of_injOn
                (fun y => ((P.revealed t).domRestrict y, (P.revealed (t + 1))ᶜ.domRestrict y))
                ?_ ?_ (toFinite _)
              · rintro y ⟨⟨hyS, -⟩, hyτ⟩
                have hyx : P.transition t y = P.transition t x := hyτ.trans hxτ.symm
                simp only [transition, Prod.mk.injEq] at hyx
                exact ⟨⟨y, ⟨hyS, hyx.1⟩, rfl⟩, ⟨y, ⟨hyS, hyx.2.1⟩, rfl⟩⟩
              · rintro y ⟨⟨-, -⟩, hyτ⟩ y' ⟨⟨-, -⟩, hy'τ⟩ hyy'
                simp only [Prod.mk.injEq, domRestrict_eq_domRestrict_iff] at hyy'
                have hnew : EqOn y y' (P.newly t) := by
                  have h := hyτ.trans hy'τ.symm
                  simp only [transition, Prod.mk.injEq, domRestrict_eq_domRestrict_iff] at h
                  exact h.2.2
                funext i
                by_cases h₁ : i ∈ P.revealed t
                · exact hyy'.1 h₁
                by_cases h₂ : i ∈ P.revealed (t + 1)
                · exact hnew ⟨h₂, h₁⟩
                · exact hyy'.2 h₂
          _ = (P.pastSide t x).ncard * (P.futureSide (t + 1) x).ncard := ncard_prod
          _ ≤ ((KL - 1) * (KR - 1)) := Nat.mul_le_mul hpast hfuture
    _ = ((KL - 1) * (KR - 1)) * P.chargedTransitionCount KL :=
        (Finset.mul_sum ..).symm

/-- The original all-transition bound follows by including uncharged transitions. -/
theorem ncard_le_of_small_sides [Finite ι] [Finite U] {KL KR : ℕ}
    (hKL : 1 < KL) (hK : KL ≤ S.ncard)
    (hsmall : ∀ t, ∀ x ∈ S, (P.pastSide t x).ncard < KL ∨ (P.futureSide t x).ncard < KR) :
    S.ncard ≤ (KL - 1) * (KR - 1) * P.transitionCount :=
  (P.ncard_le_charged_of_small_sides hKL hK hsmall).trans
    (Nat.mul_le_mul_left _ (P.chargedTransitionCount_le KL))

/-- **The frontier counting lemma.** A `K`-rectangle-free set with at least `K` elements has at
most `(K - 1) ^ 2` charged inputs per charged transition. -/
theorem ncard_le_charged [Finite ι] [Finite U] {K : ℕ}
    (hS : RectangleFree S K) (hK : K ≤ S.ncard) :
    S.ncard ≤ (K - 1) ^ 2 * P.chargedTransitionCount K := by
  by_cases hK1 : 1 < K
  · simpa only [sq] using P.ncard_le_charged_of_small_sides hK1 hK
      (fun t x _ => P.pastSide_lt_or_futureSide_lt hS t x)
  · have hEmpty : S = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hp : (P.pastSide 0 x).Nonempty := ⟨_, x, ⟨hx, rfl⟩, rfl⟩
      have hf : (P.futureSide 0 x).Nonempty := ⟨_, x, ⟨hx, rfl⟩, rfl⟩
      have hp := (ncard_pos (toFinite _)).mpr hp
      have hf := (ncard_pos (toFinite _)).mpr hf
      rcases P.pastSide_lt_or_futureSide_lt hS 0 x with h | h <;> lia
    simp [hEmpty]

/-- **The frontier counting lemma**, using all realized transitions as a supply bound. -/
theorem ncard_le [Finite ι] [Finite U] {K : ℕ} (hS : RectangleFree S K) (hK : K ≤ S.ncard) :
    S.ncard ≤ (K - 1) ^ 2 * ∑ t ∈ Finset.range P.length, (P.transition t '' S).ncard :=
  (P.ncard_le_charged hS hK).trans (Nat.mul_le_mul_left _ (P.chargedTransitionCount_le K))

end Sweep

end Frontier
