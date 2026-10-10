/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Boundary.Joint
public import Frontier.Boundary.Syndrome
public import Mathlib.LinearAlgebra.Pi

/-!
# Joint observations of a linear input code

For a linear code `range L = ker R`, record its visible coordinates together
with the partial consistency syndrome at a cut. Their joint rank is
`rank L_(past ∪ visible) + rank L_(future ∪ visible) - rank L`.
This identifies the actual observation map, including singular input maps and
redundant check equations. It does not assume independence of visible values
and the syndrome, or supply an ordering controlling this rank.

`syndromeRank_submodular` also checks the matroid connectivity property of the
partial syndrome rank. `Frontier.Layouts.Patch` uses it to optimize the signal
boundary and consistency cost in the same ordering, without a coefficient bound.
-/

@[expose] public section

namespace Frontier.LinearBoundary

open Set Module

variable {ι F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

/-- Restrict an input code to a set of its coordinates. -/
def coordinateMap (L : V →ₗ[F] (ι → F)) (Q : Set ι) : V →ₗ[F] (Q → F) :=
  (LinearMap.funLeft F F Subtype.val).comp L

@[simp] theorem coordinateMap_apply (L : V →ₗ[F] (ι → F)) (Q : Set ι)
    (x : V) (i : Q) : coordinateMap L Q x i = L x i := rfl

theorem mem_ker_coordinateMap (L : V →ₗ[F] (ι → F)) (Q : Set ι) (x : V) :
    x ∈ LinearMap.ker (coordinateMap L Q) ↔ ∀ i ∈ Q, L x i = 0 := by
  simp [LinearMap.mem_ker, funext_iff, Subtype.forall]

/-- The number of independent observations in a coordinate set. -/
noncomputable def coordinateRank (L : V →ₗ[F] (ι → F)) (P : Set ι) : ℕ :=
  finrank F (LinearMap.range (coordinateMap L P))

/-- Coordinate rank is submodular, including for singular input maps. -/
theorem coordinateRank_submodular [FiniteDimensional F V]
    (L : V →ₗ[F] (ι → F)) (P Q : Set ι) :
    coordinateRank L (P ∩ Q) + coordinateRank L (P ∪ Q) ≤
      coordinateRank L P + coordinateRank L Q := by
  have hker : LinearMap.ker (coordinateMap L (P ∪ Q)) =
      LinearMap.ker (coordinateMap L P) ⊓ LinearMap.ker (coordinateMap L Q) := by
    ext x
    simp only [mem_ker_coordinateMap, Submodule.mem_inf, mem_union, or_imp, forall_and]
  have hle : LinearMap.ker (coordinateMap L P) ⊔ LinearMap.ker (coordinateMap L Q) ≤
      LinearMap.ker (coordinateMap L (P ∩ Q)) := by
    apply sup_le
    · intro x hx
      rw [mem_ker_coordinateMap] at hx ⊢
      exact fun i hi => hx i hi.1
    · intro x hx
      rw [mem_ker_coordinateMap] at hx ⊢
      exact fun i hi => hx i hi.2
  have hdim := Submodule.finrank_mono hle
  have hid := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker (coordinateMap L P)) (LinearMap.ker (coordinateMap L Q))
  rw [← hker] at hid
  have hp := (coordinateMap L P).finrank_range_add_finrank_ker
  have hq := (coordinateMap L Q).finrank_range_add_finrank_ker
  have hi := (coordinateMap L (P ∩ Q)).finrank_range_add_finrank_ker
  have hu := (coordinateMap L (P ∪ Q)).finrank_range_add_finrank_ker
  dsimp [coordinateRank]
  lia

@[simp] theorem coordinateRank_empty (L : V →ₗ[F] (ι → F)) : coordinateRank L ∅ = 0 := by
  have h : coordinateMap L ∅ = 0 := by ext x i; exact i.2.elim
  simp [coordinateRank, h]

@[simp] theorem coordinateRank_univ [FiniteDimensional F V] (L : V →ₗ[F] (ι → F)) :
    coordinateRank L univ = finrank F (LinearMap.range L) := by
  have hker : LinearMap.ker (coordinateMap L univ) = LinearMap.ker L := by
    ext x
    simp [LinearMap.mem_ker, funext_iff]
  have hc := (coordinateMap L univ).finrank_range_add_finrank_ker
  have hl := L.finrank_range_add_finrank_ker
  rw [hker] at hc
  dsimp [coordinateRank]
  lia

/-- The number of independent consistency bits crossing a coordinate partition. -/
noncomputable def syndromeRank (L : V →ₗ[F] (ι → F)) (P : Set ι) : ℕ :=
  coordinateRank L P + coordinateRank L Pᶜ - finrank F (LinearMap.range L)

theorem syndromeRank_add [FiniteDimensional F V] (L : V →ₗ[F] (ι → F)) (P : Set ι) :
    syndromeRank L P + finrank F (LinearMap.range L) =
      coordinateRank L P + coordinateRank L Pᶜ := by
  have h := coordinateRank_submodular L P Pᶜ
  simp only [inter_compl_self, union_compl_self, coordinateRank_empty,
    coordinateRank_univ, zero_add] at h
  exact Nat.sub_add_cancel h

@[simp] theorem syndromeRank_empty [FiniteDimensional F V] (L : V →ₗ[F] (ι → F)) :
    syndromeRank L ∅ = 0 := by simp [syndromeRank]

@[simp] theorem syndromeRank_univ [FiniteDimensional F V] (L : V →ₗ[F] (ι → F)) :
    syndromeRank L univ = 0 := by simp [syndromeRank]

/-- The exact consistency cost is a submodular cut function. -/
theorem syndromeRank_submodular [FiniteDimensional F V] (L : V →ₗ[F] (ι → F)) (P Q : Set ι) :
    syndromeRank L (P ∩ Q) + syndromeRank L (P ∪ Q) ≤ syndromeRank L P + syndromeRank L Q := by
  have h := coordinateRank_submodular L P Q
  have hc := coordinateRank_submodular L Pᶜ Qᶜ
  have hp := syndromeRank_add L P
  have hq := syndromeRank_add L Q
  have hi := syndromeRank_add L (P ∩ Q)
  have hu := syndromeRank_add L (P ∪ Q)
  simp only [compl_inter, compl_union] at hi hu
  lia

/-- Keep the coordinates on one side and zero the others. -/
noncomputable def mask (P : Set ι) : (ι → F) →ₗ[F] (ι → F) where
  toFun := P.indicator
  map_add' x y := indicator_add P x y
  map_smul' a x := by
    ext i
    by_cases hi : i ∈ P <;> simp [hi]

@[simp] theorem mask_apply (P : Set ι) (x : ι → F) : mask P x = P.indicator x := rfl

/-- Visible values and the old partial syndrome, encoded together. -/
noncomputable def jointObservation (L : V →ₗ[F] (ι → F))
    (R : (ι → F) →ₗ[F] W) (P Q : Set ι) : V →ₗ[F] ((Q → F) × W) :=
  (coordinateMap L Q).prod (R.comp ((mask P).comp L))

/-- A zero joint observation splits into changes invisible on the enlarged
past and future. This is the consistency step behind the joint rank formula. -/
theorem ker_jointObservation (L : V →ₗ[F] (ι → F)) (R : (ι → F) →ₗ[F] W)
    (hR : LinearMap.ker R = LinearMap.range L) (P Q : Set ι) :
    LinearMap.ker (jointObservation L R P Q) =
      LinearMap.ker (coordinateMap L (P ∪ Q)) ⊔
        LinearMap.ker (coordinateMap L (Pᶜ ∪ Q)) := by
  ext x
  constructor
  · intro hx
    have hq : ∀ i ∈ Q, L x i = 0 := (mem_ker_coordinateMap L Q x).mp
      (congrArg Prod.fst hx)
    have hs : R (P.indicator (L x)) = 0 := congrArg Prod.snd hx
    have hr : P.indicator (L x) ∈ LinearMap.range L := by
      rw [← hR]
      exact hs
    obtain ⟨y, hy⟩ := hr
    apply Submodule.mem_sup.mpr
    refine ⟨x - y, (mem_ker_coordinateMap _ _ _).mpr ?_,
      y, (mem_ker_coordinateMap _ _ _).mpr ?_, sub_add_cancel x y⟩
    · intro i hi
      rw [L.map_sub, Pi.sub_apply, congrFun hy i]
      rcases hi with hi | hi
      · simp [hi]
      · by_cases hp : i ∈ P <;> simp [hp, hq i hi]
    · intro i hi
      rw [congrFun hy i]
      rcases hi with hi | hi
      · exact indicator_of_notMem hi _
      · by_cases hp : i ∈ P <;> simp [hp, hq i hi]
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
    have ha' := (mem_ker_coordinateMap _ _ _).mp ha
    have hb' := (mem_ker_coordinateMap _ _ _).mp hb
    have hm : P.indicator (L (a + b)) = L b := by
      funext i
      by_cases hi : i ∈ P
      · simp [hi, ha' i (Or.inl hi)]
      · simp [hi, hb' i (Or.inl hi)]
    apply Prod.ext
    · apply funext
      intro i
      change L (a + b) i = 0
      simp [ha' i (Or.inr i.2), hb' i (Or.inr i.2)]
    · change R (P.indicator (L (a + b))) = 0
      rw [hm]
      have h : L b ∈ LinearMap.range L := LinearMap.mem_range_self L b
      rwa [← hR] at h

/-- The two enlarged coordinate sets still cover every input-code coordinate. -/
theorem ker_coordinateMap_inf (L : V →ₗ[F] (ι → F)) (P Q : Set ι) :
    LinearMap.ker (coordinateMap L (P ∪ Q)) ⊓
      LinearMap.ker (coordinateMap L (Pᶜ ∪ Q)) = LinearMap.ker L := by
  ext x
  rw [Submodule.mem_inf, mem_ker_coordinateMap, mem_ker_coordinateMap,
    LinearMap.mem_ker]
  constructor
  · rintro ⟨hp, hf⟩
    funext i
    by_cases hi : i ∈ P
    · exact hp i (Or.inl hi)
    · exact hf i (Or.inl hi)
  · intro h
    constructor <;> intro i _ <;> exact congrFun h i

/-- Exact rank of the visible values and the partial syndrome. No injectivity
of the supplied linear map or independence of the check equations is needed. -/
theorem finrank_jointObservation [FiniteDimensional F V]
    (L : V →ₗ[F] (ι → F)) (R : (ι → F) →ₗ[F] W)
    (hR : LinearMap.ker R = LinearMap.range L) (P Q : Set ι) :
    finrank F (LinearMap.range (jointObservation L R P Q)) =
      finrank F (LinearMap.range (coordinateMap L (P ∪ Q))) +
        finrank F (LinearMap.range (coordinateMap L (Pᶜ ∪ Q))) -
          finrank F (LinearMap.range L) := by
  have hs := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker (coordinateMap L (P ∪ Q)))
    (LinearMap.ker (coordinateMap L (Pᶜ ∪ Q)))
  rw [← ker_jointObservation L R hR P Q, ker_coordinateMap_inf L P Q] at hs
  have hj := (jointObservation L R P Q).finrank_range_add_finrank_ker
  have hp := (coordinateMap L (P ∪ Q)).finrank_range_add_finrank_ker
  have hf := (coordinateMap L (Pᶜ ∪ Q)).finrank_range_add_finrank_ker
  have hl := L.finrank_range_add_finrank_ker
  lia

/-- With no separately visible coordinates, the observation rank is exactly the
submodular consistency cost of the coordinate partition. -/
theorem finrank_partialSyndrome [FiniteDimensional F V]
    (L : V →ₗ[F] (ι → F)) (R : (ι → F) →ₗ[F] W)
    (hR : LinearMap.ker R = LinearMap.range L) (P : Set ι) :
    finrank F (LinearMap.range (R.comp ((mask P).comp L))) = syndromeRank L P := by
  have hker : LinearMap.ker (jointObservation L R P ∅) =
      LinearMap.ker (R.comp ((mask P).comp L)) := by
    ext x
    simp [jointObservation, LinearMap.mem_ker, funext_iff]
  have hj := finrank_jointObservation L R hR P ∅
  rw [Set.union_empty, Set.union_empty] at hj
  have hjn := (jointObservation L R P ∅).finrank_range_add_finrank_ker
  have hsn := (R.comp ((mask P).comp L)).finrank_range_add_finrank_ker
  rw [hker] at hjn
  dsimp [syndromeRank, coordinateRank]
  lia

/-- Exact cardinality of the joint code over a finite field. The identity also
uses the usual `Nat.card` convention when the field is infinite. -/
theorem ncard_jointObservation [FiniteDimensional F V]
    (L : V →ₗ[F] (ι → F)) (R : (ι → F) →ₗ[F] W)
    (hR : LinearMap.ker R = LinearMap.range L) (P Q : Set ι) :
    (range (jointObservation L R P Q)).ncard =
      Nat.card F ^ (finrank F (LinearMap.range (coordinateMap L (P ∪ Q))) +
        finrank F (LinearMap.range (coordinateMap L (Pᶜ ∪ Q))) -
          finrank F (LinearMap.range L)) := by
  rw [← LinearMap.coe_range, ← Nat.card_coe_set_eq]
  change Nat.card ↥(LinearMap.range (jointObservation L R P Q)) = _
  rw [Module.natCard_eq_pow_finrank (K := F), finrank_jointObservation L R hR]

/-- Translating the input code translates its joint observations and leaves
their exact count unchanged. -/
theorem ncard_affine_jointObservation [FiniteDimensional F V]
    (L : V →ₗ[F] (ι → F)) (R : (ι → F) →ₗ[F] W)
    (hR : LinearMap.ker R = LinearMap.range L) (P Q : Set ι) (a : ι → F) :
    (range (fun x => jointObservation LinearMap.id R P Q (a + L x))).ncard =
      Nat.card F ^ (finrank F (LinearMap.range (coordinateMap L (P ∪ Q))) +
        finrank F (LinearMap.range (coordinateMap L (Pᶜ ∪ Q))) -
          finrank F (LinearMap.range L)) := by
  have heq : (fun x => jointObservation LinearMap.id R P Q (a + L x)) =
      (fun z => jointObservation LinearMap.id R P Q a + z) ∘
        jointObservation L R P Q := by
    funext x
    exact (jointObservation LinearMap.id R P Q).map_add a (L x)
  rw [heq, Set.range_comp, ncard_image_of_injective _ (fun _ _ h => add_left_cancel h)]
  exact ncard_jointObservation L R hR P Q

end Frontier.LinearBoundary

namespace Frontier.Sweep

open Set Module LinearBoundary

variable {ι F V W M : Type*} [Finite ι] [Field F] [Finite F]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  [AddCommGroup W] [Module F W] {S : Set (ι → F)}

/-- Supply for a sweep with consistent linear inputs. Count the non-input part
of each code separately, but visible input values and the syndrome jointly.
The code must determine the original complete transition on consistent inputs. -/
theorem transitionCount_restrictLinear_le_joint (P : Sweep S M)
    (L : V →ₗ[F] (ι → F)) (R : (ι → F) →ₗ[F] W)
    (hR : LinearMap.ker R = LinearMap.range L)
    (hmono : ∀ t < P.length, P.revealed t ⊆ P.revealed (t + 1))
    (Q : ℕ → Set ι) {D : ℕ → Type*}
    (code : ∀ t, (ι → F) → D t) (C : ∀ t, Set (D t))
    (hC : ∀ t < P.length, (C t).Finite)
    (hmem : ∀ t < P.length, ∀ x ∈ S ∩ range L, code t x ∈ C t)
    (hdet : ∀ t < P.length, ∀ x ∈ S ∩ range L, ∀ y ∈ S ∩ range L,
      code t x = code t y → coordinateMap LinearMap.id (Q t) x =
        coordinateMap LinearMap.id (Q t) y → P.transition t x = P.transition t y) :
    (P.restrictHom R.toAddMonoidHom 0).transitionCount ≤
      ∑ t ∈ Finset.range P.length, (C t).ncard *
        Nat.card F ^ (finrank F (LinearMap.range (coordinateMap L (P.revealed t ∪ Q t))) +
          finrank F (LinearMap.range (coordinateMap L ((P.revealed t)ᶜ ∪ Q t))) -
            finrank F (LinearMap.range L)) := by
  have hvalid {x : ι → F} (hx : x ∈ S ∩ R.toAddMonoidHom ⁻¹' {0}) :
      x ∈ S ∩ range L := by
    refine ⟨hx.1, ?_⟩
    change x ∈ LinearMap.range L
    rw [← hR]
    exact hx.2
  have hfinite (t : ℕ) : (range (jointObservation L R (P.revealed t) (Q t))).Finite := by
    change (range (jointObservation LinearMap.id R (P.revealed t) (Q t) ∘ L)).Finite
    rw [Set.range_comp]
    exact (toFinite (range L)).image _
  have h := (P.restrictHom R.toAddMonoidHom 0).transitionCount_le_codes
    (fun t x => (code t x, jointObservation LinearMap.id R (P.revealed t) (Q t) x))
    (fun t => C t ×ˢ range (jointObservation L R (P.revealed t) (Q t)))
    (fun t ht => (hC t ht).prod (hfinite t)) (fun t ht x hx => by
      obtain ⟨z, hz⟩ := (hvalid hx).2
      exact ⟨hmem t ht x (hvalid hx), ⟨z, by rw [← hz]; rfl⟩⟩)
    (fun t ht x hx y hy hxy => P.restrictHom_transition_eq R.toAddMonoidHom 0
      (hmono t ht) (hdet t ht x (hvalid hx) y (hvalid hy)
        (congrArg Prod.fst hxy) (congrArg (fun z => z.2.1) hxy))
      (congrArg (fun z => z.2.2) hxy))
  simpa only [restrictHom, ncard_prod, ncard_jointObservation L R hR] using h

end Frontier.Sweep
