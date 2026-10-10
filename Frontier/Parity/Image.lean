/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Parity.Support

/-!
# Removing the unobserved kernel

When membership in `S` depends only on an additive observation, its image remains
sumset-free. The summand sets in the image's ambient space need not lie in the
observation range: translate them in opposite directions before lifting them.
For linear observations, each fiber costs at most `q^nullity` inputs.
-/

@[expose] public section

namespace Frontier

open Set Module

/-- The image of a sumset-free set remains sumset-free when the set is saturated
under the observation. No choice of a linear complement is required. -/
theorem SumsetFree.image_addHom_of_saturated {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] {S : Set G} {K : ℕ}
    (hS : SumsetFree S K) (f : G →+ H)
    (hsat : ∀ x, f x ∈ f '' S → x ∈ S) : SumsetFree (f '' S) K := by
  classical
  have hK : 0 < K := by
    have h := hS ∅ ∅ (by simp)
    simpa using h
  intro A B hAB
  rcases A.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · exact Or.inl (by simpa using hK)
  rcases B.eq_empty_or_nonempty with rfl | ⟨b₀, hb₀⟩
  · exact Or.inr (by simpa using hK)
  let g := Function.invFun f
  have hg : ∀ z ∈ range f, f (g z) = z := by
    rintro _ ⟨x, rfl⟩
    exact Function.apply_invFun_apply
  have hA : ∀ a ∈ A, a + b₀ ∈ range f := fun a ha =>
    image_subset_range f S (hAB a ha b₀ hb₀)
  have hB : ∀ b ∈ B, b - b₀ ∈ range f := by
    intro b hb
    obtain ⟨x, hx, hfx⟩ := hAB a₀ ha₀ b hb
    obtain ⟨y, hy, hfy⟩ := hAB a₀ ha₀ b₀ hb₀
    refine ⟨x - y, ?_⟩
    rw [f.map_sub, hfx, hfy]
    abel
  have hiA : InjOn (fun a => g (a + b₀)) A := by
    intro a ha a' ha' h
    have h' := congrArg f h
    rw [hg _ (hA a ha), hg _ (hA a' ha')] at h'
    exact add_right_cancel h'
  have hiB : InjOn (fun b => g (b - b₀)) B := by
    intro b hb b' hb' h
    have h' := congrArg f h
    rw [hg _ (hB b hb), hg _ (hB b' hb')] at h'
    exact sub_left_injective h'
  have h := hS ((fun a => g (a + b₀)) '' A) ((fun b => g (b - b₀)) '' B) (by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    apply hsat
    rw [f.map_add, hg _ (hA a ha), hg _ (hB b hb)]
    have heq : a + b₀ + (b - b₀) = a + b := by abel
    rw [heq]
    exact hAB a ha b hb)
  rwa [hiA.ncard_image, hiB.ncard_image] at h

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

/-- A linear image loses at most one kernel's worth of accepting inputs. -/
theorem ncard_le_pow_finrank_ker_mul_image [Finite V] [FiniteDimensional F V]
    (L : V →ₗ[F] W) (S : Set V) :
    S.ncard ≤ Nat.card F ^ finrank F (LinearMap.ker L) * (L '' S).ncard := by
  apply ncard_le_mul_ncard_image (toFinite S) L
  intro z
  rcases (S ∩ L ⁻¹' {z}).eq_empty_or_nonempty with h | ⟨x₀, hx₀⟩
  · simp [h]
  have h : (S ∩ L ⁻¹' {z}).ncard ≤ (LinearMap.ker L : Set V).ncard := by
    refine ncard_le_ncard_of_injOn (fun x => x - x₀) ?_ ?_ (toFinite _)
    · rintro x ⟨hx, hLx⟩
      change L (x - x₀) = 0
      rw [L.map_sub, show L x = z from hLx,
        show L x₀ = z from hx₀.2, sub_self]
    · exact fun _ _ _ _ h => sub_left_injective h
  rw [← Nat.card_coe_set_eq] at h
  change (S ∩ L ⁻¹' {z}).ncard ≤ Nat.card ↥(LinearMap.ker L) at h
  rwa [Module.natCard_eq_pow_finrank (K := F)] at h

/-- A large hard set is still above the charging threshold after discarding
the unobserved kernel. -/
theorem SumsetFree.le_ncard_image_of_saturated [Finite V] [FiniteDimensional F V]
    {S : Set V} {K : ℕ} (hS : SumsetFree S K) (hbig : K ^ 2 ≤ S.ncard)
    (L : V →ₗ[F] W)
    (hobs : ∀ x y, L x = L y → (x ∈ S ↔ y ∈ S)) : K ≤ (L '' S).ncard := by
  have hK : 0 < K := by
    have h := hS ∅ ∅ (by simp)
    simpa using h
  have hk := hS.pow_finrank_ker_lt
    ((Nat.le_self_pow two_ne_zero K).trans hbig) L hobs
  have himage := ncard_le_pow_finrank_ker_mul_image L S
  by_contra! hsmall
  have hlt := Nat.mul_lt_mul_of_lt_of_lt hk hsmall
  rw [← pow_two] at hlt
  lia

end Frontier
