/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.AdditiveSweep
public import Frontier.AverageCase.Bias
public import Frontier.AverageCase.Extractor
public import Mathlib.Algebra.Ring.BooleanRing

/-!
# Weighted bounds for unambiguous additive generation

A coherent additive sweep recovers the chosen prefix and suffix contributions after
splicing, and splices the whole message trace. Unique accepting paths give this property.
Consequently its message classes are direct sumsets, and deleting one preserves coherence.
Sam McGuire's disjoint peeling argument for coordinate sweeps then extends to additive
sweeps. Arbitrary ambiguous additive generators are not covered by this theorem.
-/

@[expose] public section

namespace Frontier

open Set

variable {G M : Type*}

/-- A budget for thick sumsets with unique representations. Flat-source bias controls
these sets without replacing uniform inputs by a multiplicity-weighted distribution. -/
def AdditiveBudget [Add G] [Finite G] (w cost : G → ℝ) (KL KR : ℕ) : Prop :=
  ∀ A B : Set G, KL ≤ A.ncard → KR ≤ B.ncard →
    InjOn (fun p : G × G => p.1 + p.2) (A ×ˢ B) →
    |sumOn w ((fun p : G × G => p.1 + p.2) '' (A ×ˢ B))| ≤
      sumOn cost ((fun p : G × G => p.1 + p.2) '' (A ×ˢ B))

namespace AdditiveSweep

variable [AddMonoid G] {S : Set G} (P : AdditiveSweep S M)

/-- Splicing recovers both summands and splices the chosen message traces. This is the
extra hypothesis needed for uniform-input bounds; reconstruction alone is insufficient. -/
def Coherent : Prop :=
  ∀ t, ∀ x ∈ S, ∀ y ∈ S, P.message t x = P.message t y →
    let z := P.past t x + P.future t y
    P.past t z = P.past t x ∧ P.future t z = P.future t y ∧
      (∀ u, u ≤ t → P.message u z = P.message u x) ∧
      (∀ u, t ≤ u → P.message u z = P.message u y)

/-- Each coherent message class is precisely the sum of its prefix and suffix sets. -/
theorem Coherent.peers_eq_sumset (hP : P.Coherent) (t : ℕ) (x : G) :
    P.peers t x = (fun p : G × G => p.1 + p.2) ''
      (P.pastSide t x ×ˢ P.futureSide t x) := by
  apply subset_antisymm
  · intro y hy
    exact ⟨(P.past t y, P.future t y), ⟨⟨y, hy, rfl⟩, ⟨y, hy, rfl⟩⟩,
      P.reconstruct t y hy.1⟩
  · rintro _ ⟨⟨_, _⟩, ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, rfl⟩
    have hab := ha.2.trans hb.2.symm
    exact ⟨P.splice t a ha.1 b hb.1 hab,
      ((hP t a ha.1 b hb.1 hab).2.2.1 t le_rfl).trans ha.2⟩

/-- The sumset in a coherent message class has no collisions. -/
theorem Coherent.add_injOn (hP : P.Coherent) (t : ℕ) (x : G) :
    InjOn (fun p : G × G => p.1 + p.2) (P.pastSide t x ×ˢ P.futureSide t x) := by
  rintro ⟨_, _⟩ ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
    ⟨_, _⟩ ⟨⟨c, hc, rfl⟩, ⟨d, hd, rfl⟩⟩ he
  have hab := hP t a ha.1 b hb.1 (ha.2.trans hb.2.symm)
  have hcd := hP t c hc.1 d hd.1 (hc.2.trans hd.2.symm)
  exact Prod.ext (hab.1.symm.trans ((congrArg (P.past t) he).trans hcd.1))
    (hab.2.1.symm.trans ((congrArg (P.future t) he).trans hcd.2.1))

/-- Deleting one state retains exactly the inputs whose unique trace avoids it. -/
noncomputable def erase (hP : P.Coherent) (t : ℕ) (x : G) :
    AdditiveSweep (S \ P.peers t x) M where
  length := P.length
  past := P.past
  future := P.future
  emit := P.emit
  message := P.message
  past_zero a ha := P.past_zero a ha.1
  past_length a ha := P.past_length a ha.1
  message_length a ha b hb := P.message_length a ha.1 b hb.1
  reconstruct u a ha := P.reconstruct u a ha.1
  step u a ha := P.step u a ha.1
  splice u a ha b hb hab := by
    refine ⟨P.splice u a ha.1 b hb.1 hab, ?_⟩
    intro hz
    have H := hP u a ha.1 b hb.1 hab
    rcases le_total t u with h | h
    · exact ha.2 ⟨ha.1, (H.2.2.1 t h).symm.trans hz.2⟩
    · exact hb.2 ⟨hb.1, (H.2.2.2 t h).symm.trans hz.2⟩

theorem Coherent.erase (hP : P.Coherent) (t : ℕ) (x : G) :
    (P.erase hP t x).Coherent := by
  intro u a ha b hb hab
  exact hP u a ha.1 b hb.1 hab

theorem transitionCount_erase_le [Finite G] (hP : P.Coherent) (t : ℕ) (x : G) :
    (P.erase hP t x).transitionCount ≤ P.transitionCount := by
  refine Finset.sum_le_sum fun u _ => ?_
  change (P.transition u '' (S \ P.peers t x)).ncard ≤ (P.transition u '' S).ncard
  exact ncard_le_ncard (image_mono sdiff_subset) ((toFinite S).image _)

theorem transitionCount_pos [Finite G] (hL : 0 < P.length) (hS : S.Nonempty) :
    0 < P.transitionCount := by
  have hi : 0 < (P.transition 0 '' S).ncard :=
    (ncard_pos (toFinite _)).mpr (hS.image _)
  unfold transitionCount
  exact hi.trans_le (Finset.single_le_sum (f := fun t => (P.transition t '' S).ncard)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hL))

/-- **Weighted peeling.** A shared nonnegative budget on thick direct sumsets is paid once;
only the residual thin sweep pays its maximum atom times the transition count. -/
theorem abs_sumOn_le_of_budget [Finite G] (hP : P.Coherent) (hL : 0 < P.length)
    {KL KR : ℕ} (hKL : 1 < KL) (hKR : 1 < KR)
    {w cost : G → ℝ} {a : ℝ} (ha : 0 ≤ a) (hw : ∀ x, |w x| ≤ a)
    (hc : ∀ x, 0 ≤ cost x) (hrect : AdditiveBudget w cost KL KR) :
    |sumOn w S| ≤ sumOn cost S + a * ((KL - 1) * (KR - 1) * P.transitionCount : ℕ) := by
  classical
  induction hn : S.ncard using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases hthick : ∃ t x, x ∈ S ∧ KL ≤ (P.pastSide t x).ncard ∧ KR ≤ (P.futureSide t x).ncard
    · obtain ⟨t, x, hx, hA, hB⟩ := hthick
      let R := P.peers t x
      have hR : R ⊆ S := fun _ hy => hy.1
      have hxR : x ∈ R := ⟨hx, rfl⟩
      have hlt : (S \ R).ncard < n := by
        rw [← hn]
        exact ncard_lt_ncard (ssubset_iff_subset_ne.mpr ⟨sdiff_subset,
          fun he => (show x ∈ S \ R from by rw [he]; exact hx).2 hxR⟩)
      have hbudget : |sumOn w R| ≤ sumOn cost R := by
        rw [show R = (fun p : G × G => p.1 + p.2) '' (P.pastSide t x ×ˢ P.futureSide t x) from
          Coherent.peers_eq_sumset P hP t x]
        exact hrect _ _ hA hB (hP.add_injOn P t x)
      have hrest := ih _ hlt (P.erase hP t x) (Coherent.erase P hP t x) hL rfl
      have hcount : a * (((KL - 1) * (KR - 1) * (P.erase hP t x).transitionCount : ℕ) : ℝ) ≤
          a * ((KL - 1) * (KR - 1) * P.transitionCount : ℕ) := by
        apply mul_le_mul_of_nonneg_left _ ha
        exact_mod_cast Nat.mul_le_mul_left _ (P.transitionCount_erase_le hP t x)
      rw [sumOn_sdiff w hR, sumOn_sdiff cost hR]
      exact (abs_add_le _ _).trans (by linarith)
    · have hsmall : ∀ t, ∀ x ∈ S,
          (P.pastSide t x).ncard < KL ∨ (P.futureSide t x).ncard < KR := by
        push Not at hthick
        intro t x hx
        by_cases hA : KL ≤ (P.pastSide t x).ncard
        · exact Or.inr (hthick t x hx hA)
        · exact Or.inl (not_le.mp hA)
      have hcard : S.ncard ≤ (KL - 1) * (KR - 1) * P.transitionCount := by
        by_cases hK : KL ≤ S.ncard
        · exact P.ncard_le_of_small_sides hKL hK hsmall
        · rcases S.eq_empty_or_nonempty with hS | hS
          · simp [hS]
          · have hD := P.transitionCount_pos hL hS
            have hB : 1 ≤ KR - 1 := by lia
            have : KL - 1 ≤ (KL - 1) * (KR - 1) * P.transitionCount := by
              nlinarith [Nat.mul_le_mul_left (KL - 1) hB]
            lia
      have hcardR : a * S.ncard ≤ a * ((KL - 1) * (KR - 1) * P.transitionCount : ℕ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) ha
      exact (abs_sumOn_le hw S).trans (by linarith [sumOn_nonneg hc S])


end AdditiveSweep


/-- Flat XOR-source bias pays the budget of every thick direct sumset. Mathlib's
Boolean-ring addition is XOR, so no change of alphabet is needed. -/
theorem FlatSumsetBias.additiveBudget {ι : Type*} [Finite ι]
    {f : (ι → Bool) → Bool} {K : ℕ} {β : ℝ} (hf : FlatSumsetBias f K β) :
    AdditiveBudget (fun x => boolSign (f x)) (fun _ => β) K K := by
  classical
  intro A B hA hB hi
  rw [sumOn_const, hi.ncard_image, ncard_prod]
  have he : sumOn (fun x => boolSign (f x))
      ((fun p : (ι → Bool) × (ι → Bool) => p.1 + p.2) '' (A ×ˢ B)) =
      sumOn (fun x => sumOn (fun y => boolSign (f (xorInputs x y))) B) A := by
    unfold sumOn
    rw [Set.Finite.toFinset_image _ (toFinite (A ×ˢ B)),
      Finset.sum_image (fun a ha b hb hab => hi
        ((toFinite (A ×ˢ B)).mem_toFinset.mp ha)
        ((toFinite (A ×ˢ B)).mem_toFinset.mp hb) hab),
      ← Set.Finite.toFinset_prod (toFinite A) (toFinite B)]
    exact Finset.sum_product _ _ _
  rw [he]
  exact hf A B hA hB

/-- **Uniform average-case additive bound.** Each output class has its own coherent
sweep. The remainder charges their total transition count once, with the factor `1/2`
from converting signed correlation to agreement. `β` denotes signed bias (twice the
usual statistical error of an extracted bit). -/
theorem agreement_le_of_additive_sweeps {ι : Type*} [Finite ι]
    {f g : (ι → Bool) → Bool} {K : ℕ} {β : ℝ}
    (hf : FlatSumsetBias f K β) (hK : 1 < K) (hβ : 0 ≤ β)
    (P : ∀ b : Bool, AdditiveSweep {x | g x = b} M)
    (hP : ∀ b, (P b).Coherent) (hL : ∀ b, 0 < (P b).length) :
    agreement f g ≤ (1 + β) / 2 +
      ((K - 1) ^ 2 * ((P true).transitionCount + (P false).transitionCount) : ℕ) /
        (2 * (2 : ℝ) ^ Nat.card ι) := by
  have H := agreement_le_of_output_biases f g (fun b => by
    have H := (P b).abs_sumOn_le_of_budget (hP b) (hL b) hK hK
      (a := 1) (by norm_num) (fun x => (abs_boolSign (f x)).le)
      (fun _ => hβ) hf.additiveBudget
    simpa only [sumOn_const, one_mul, ← sq] using H)
  simpa only [Nat.card_fun, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool,
    Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_mul, Nat.cast_add, mul_add, add_div] using H

end Frontier
