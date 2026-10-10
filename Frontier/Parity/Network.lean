/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Parity.Image
public import Frontier.Network.Read

/-!
# Frontier bounds for the linear inputs actually read

First discard the unobserved kernel of the independent input. Next impose the
linear consistency promise only among physical inputs that the network reads.
The two losses are `q^nullity` and `q^codimension`; they are different quantities.
The former is less than `K` by sumset hardness. The latter is retained explicitly.
This yields a finite promise-correct network bound without assuming anything
about acceptance on inconsistent supplied inputs or paying for unused parities.
-/

@[expose] public section

namespace Frontier

open Set Module LinearBoundary

variable {F V ι M : Type*} [Field F] [Finite F] [AddCommGroup V] [Module F V]
  [Finite V] [FiniteDimensional F V] [Finite ι]

/-- Enforce an arbitrary supplied linear code using its quotient syndrome.
Nullity accounts for original inputs with the same observation; codimension
accounts for consistency among the supplied observations. -/
theorem ncard_le_linear_sweep (L : V →ₗ[F] (ι → F))
    {S : Set V} {T : Set (ι → F)} {K : ℕ}
    (hS : SumsetFree S K) (hbig : K ^ 2 ≤ S.ncard)
    (hT : ∀ x, L x ∈ T ↔ x ∈ S) (P : Sweep T M)
    (hmono : ∀ t < P.length, P.revealed t ⊆ P.revealed (t + 1)) :
    S.ncard ≤ Nat.card F ^ finrank F (LinearMap.ker L) * (K - 1) ^ 2 *
      Nat.card F ^ (Nat.card ι - finrank F (LinearMap.range L)) * P.transitionCount := by
  let _ := Fintype.ofFinite ι
  let R := (LinearMap.range L).mkQ
  have hobs : ∀ x y, L x = L y → (x ∈ S ↔ y ∈ S) := by
    intro x y hxy
    rw [← hT x, ← hT y, hxy]
  have hsat : ∀ x, L x ∈ L '' S → x ∈ S := by
    rintro x ⟨y, hy, hxy⟩
    exact (hobs y x hxy).mp hy
  have hfree := hS.image_addHom_of_saturated L.toAddMonoidHom hsat
  have hcard := hS.le_ncard_image_of_saturated hbig L hobs
  have hset : T ∩ R ⁻¹' {0} = L '' S := by
    ext z
    change (z ∈ T ∧ R z = 0) ↔ z ∈ L '' S
    rw [← LinearMap.mem_ker, show LinearMap.ker R = LinearMap.range L from
      Submodule.ker_mkQ _]
    constructor
    · rintro ⟨hz, x, rfl⟩
      exact ⟨x, (hT x).mp hz, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(hT x).mpr hx, LinearMap.mem_range_self L x⟩
  have hr : finrank F (LinearMap.range R) =
      Nat.card ι - finrank F (LinearMap.range L) := by
    have h := R.finrank_range_add_finrank_ker
    rw [Submodule.ker_mkQ, Module.finrank_pi, ← Nat.card_eq_fintype_card] at h
    lia
  have hdemand := (P.restrictHom R.toAddMonoidHom 0).ncard_le
    (by
      change RectangleFree (T ∩ R ⁻¹' {0}) K
      rw [hset]
      exact hfree.rectangleFree)
    (by
      change K ≤ (T ∩ R ⁻¹' {0}).ncard
      rwa [hset])
  have hsupply := P.transitionCount_restrictLinear_le R 0 hmono
  rw [hr] at hsupply
  change (T ∩ R ⁻¹' {0}).ncard ≤ _ at hdemand
  rw [hset] at hdemand
  calc S.ncard
      ≤ Nat.card F ^ finrank F (LinearMap.ker L) * (L '' S).ncard :=
        ncard_le_pow_finrank_ker_mul_image L S
    _ ≤ Nat.card F ^ finrank F (LinearMap.ker L) *
        ((K - 1) ^ 2 * (Nat.card F ^ (Nat.card ι - finrank F (LinearMap.range L)) *
          P.transitionCount)) :=
        Nat.mul_le_mul_left _ (hdemand.trans (Nat.mul_le_mul_left _ hsupply))
    _ = _ := by ring

/-- A network with free supplied linear inputs pays only for the rank and
redundancy of the forms it actually reads. The graph and layout are unchanged. -/
theorem Network.ncard_le_of_linear_inputs {J E : Type*} [Finite E]
    (N : Network F ι J E) (L : V →ₗ[F] (ι → F)) {S : Set V} {K : ℕ}
    (hS : SumsetFree S K) (hbig : K ^ 2 ≤ S.ncard)
    (hN : ∀ x, L x ∈ N.accepted ↔ x ∈ S) (π : Layout J)
    {w d m : ℕ} (hw : ∀ t, (N.frontier π t).ncard ≤ w) (hd : N.MaxDegreeLE d)
    (hm : ∀ v, (N.readAt v).ncard ≤ m) :
    S.ncard ≤ Nat.card F ^ finrank F (LinearMap.ker (coordinateMap L N.read)) *
      (K - 1) ^ 2 * Nat.card F ^ (N.read.ncard - coordinateRank L N.read) *
        (Nat.card J * Nat.card F ^ (w + d + m) + 1) := by
  have hpromise : ∀ x, coordinateMap L N.read x ∈ N.restrictRead.accepted ↔ x ∈ S :=
    fun x => (N.mem_accepted_restrictRead (L x)).trans (hN x)
  have h := ncard_le_linear_sweep (coordinateMap L N.read) hS hbig hpromise
    (N.restrictRead.sweep π) (fun t _ => N.restrictRead.revealedBy_mono π (by lia))
  have hsupply := N.restrictRead.transitionCount_sweep_le π hw hd
    (fun v => (N.ncard_readAt_restrictRead_le v).trans (hm v))
  simp only [N.read_restrictRead, compl_univ, ncard_empty, pow_zero] at hsupply
  rw [Nat.card_coe_set_eq] at h
  exact h.trans (Nat.mul_le_mul_left _ hsupply)

/-- In logarithmic form, the only new linear-sized term is the redundancy of
the read forms. The unobserved kernel has been absorbed into `3 log_q K`. -/
theorem Network.logb_ncard_le_of_linear_inputs {J E : Type*} [Finite E]
    (N : Network F ι J E) (L : V →ₗ[F] (ι → F)) {S : Set V} {K : ℕ}
    (hS : SumsetFree S K) (hbig : K ^ 2 ≤ S.ncard)
    (hN : ∀ x, L x ∈ N.accepted ↔ x ∈ S) (π : Layout J)
    {w d m : ℕ} (hw : ∀ t, (N.frontier π t).ncard ≤ w) (hd : N.MaxDegreeLE d)
    (hm : ∀ v, (N.readAt v).ncard ≤ m) :
    Real.logb (Nat.card F) S.ncard ≤ w + (d + m) +
      (N.read.ncard - coordinateRank L N.read : ℕ) +
        3 * Real.logb (Nat.card F) K + Real.logb (Nat.card F) (Nat.card J + 1) := by
  set q := Nat.card F
  set v := Nat.card J
  set c := N.read.ncard - coordinateRank L N.read
  have hq : 1 < q := Finite.one_lt_card
  have hK : 0 < K := by
    have h := hS ∅ ∅ (by simp)
    simpa using h
  have hk := N.pow_finrank_read_ker_lt L hS
    ((Nat.le_self_pow two_ne_zero K).trans hbig) hN
  have hnat : S.ncard ≤ K ^ 3 * (v + 1) * q ^ (w + d + m + c) := by
    calc S.ncard
        ≤ q ^ finrank F (LinearMap.ker (coordinateMap L N.read)) * (K - 1) ^ 2 *
          q ^ c * (v * q ^ (w + d + m) + 1) :=
            N.ncard_le_of_linear_inputs L hS hbig hN π hw hd hm
      _ ≤ K * K ^ 2 * q ^ c * (v * q ^ (w + d + m) + 1) := by
          gcongr
          exact Nat.sub_le K 1
      _ ≤ K * K ^ 2 * q ^ c * ((v + 1) * q ^ (w + d + m)) := by
          gcongr
          have hpow : 1 ≤ q ^ (w + d + m) := Nat.one_le_iff_ne_zero.mpr (by positivity)
          nlinarith
      _ = _ := by rw [pow_add]; ring
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hSpos : (0 : ℝ) < S.ncard := by
    exact_mod_cast (lt_of_lt_of_le (pow_pos hK 2) hbig)
  calc Real.logb q S.ncard
      ≤ Real.logb q ((K : ℝ) ^ 3 * (v + 1) * (q : ℝ) ^ (w + d + m + c)) :=
        Real.logb_le_logb_of_le hqR hSpos (by exact_mod_cast hnat)
    _ = _ := by
        rw [Real.logb_mul (by positivity) (by positivity),
          Real.logb_mul (by positivity) (by positivity),
          Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hqR]
        push_cast
        ring

end Frontier
