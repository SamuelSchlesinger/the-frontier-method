/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.AdditiveSweep
public import Frontier.Boundary.Observation
public import Mathlib.LinearAlgebra.Pi

/-!
# Hardness under supplied parity inputs

For an input map `p`, `inputGraph p S` is the set of consistent accepting pairs
`(x, p x)`. Supplying these values preserves the number of accepting inputs and
sumset-freeness. The latter holds even for nonlinear `p`: any sumset in the graph
projects injectively on each of its two sides after fixing an element of the other
side. An additive sweep enforcing the promise therefore has the same charging demand.

An invertible additive change of input basis also preserves the full circuit lower
bound. This is the case of independent parity inputs. For redundantly supplied
parities, graph hardness alone is insufficient: the circuit is constrained only on
consistent pairs, whereas its ordinary frontier can splice inconsistent pairs.
This file does not assert a circuit supply bound for a linear number of redundant
free parity inputs. It constructs the consistency demand and combines it with
the exact joint code for visible supplied values and partial syndromes, retaining
the resulting layout-dependent rank in `ncard_le_parity_joint_codes`.
-/

@[expose] public section

namespace Frontier

open Set Cslib.Circuits Filter Asymptotics

variable {G H M : Type*}

/-- Consistent accepting pairs when `p x` is supplied together with `x`. -/
def inputGraph (p : G → H) (S : Set G) : Set (G × H) :=
  (fun x => (x, p x)) '' S

@[simp] theorem mem_inputGraph {p : G → H} {S : Set G} {z : G × H} :
    z ∈ inputGraph p S ↔ z.1 ∈ S ∧ z.2 = p z.1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx, rfl⟩
  · rintro ⟨hx, hp⟩
    exact ⟨z.1, hx, Prod.ext rfl hp.symm⟩

@[simp] theorem ncard_inputGraph (p : G → H) (S : Set G) :
    (inputGraph p S).ncard = S.ncard :=
  ncard_image_of_injective _ fun _ _ h => congrArg Prod.fst h

/-- Redundant supplied values preserve sumset-freeness of the consistent set.
No linearity of the supplied map is needed for this demand statement. -/
theorem SumsetFree.inputGraph [Add G] [AddCancelMonoid H] {S : Set G} {K : ℕ}
    (hS : SumsetFree S K) (p : G → H) : SumsetFree (inputGraph p S) K := by
  intro A B hAB
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · obtain ⟨a₀, ha₀⟩ := hA
      obtain ⟨b₀, hb₀⟩ := hB
      have hinjA : InjOn Prod.fst A := by
        intro a ha a' ha' h
        apply Prod.ext h
        apply add_right_cancel (b := b₀.2)
        have h₁ := (mem_inputGraph.mp (hAB a ha b₀ hb₀)).2
        have h₂ := (mem_inputGraph.mp (hAB a' ha' b₀ hb₀)).2
        change a.2 + b₀.2 = p (a.1 + b₀.1) at h₁
        change a'.2 + b₀.2 = p (a'.1 + b₀.1) at h₂
        rw [h] at h₁
        exact h₁.trans h₂.symm
      have hinjB : InjOn Prod.fst B := by
        intro b hb b' hb' h
        apply Prod.ext h
        apply add_left_cancel (a := a₀.2)
        have h₁ := (mem_inputGraph.mp (hAB a₀ ha₀ b hb)).2
        have h₂ := (mem_inputGraph.mp (hAB a₀ ha₀ b' hb')).2
        change a₀.2 + b.2 = p (a₀.1 + b.1) at h₁
        change a₀.2 + b'.2 = p (a₀.1 + b'.1) at h₂
        rw [h] at h₁
        exact h₁.trans h₂.symm
      have h := hS (Prod.fst '' A) (Prod.fst '' B) (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        exact (mem_inputGraph.mp (hAB a ha b hb)).1)
      rwa [hinjA.ncard_image, hinjB.ncard_image] at h
    · exact Or.inr (by
        rw [not_nonempty_iff_eq_empty.mp hB, ncard_empty]
        have := hS ∅ ∅ (by simp)
        simpa using this)
  · exact Or.inl (by
      rw [not_nonempty_iff_eq_empty.mp hA, ncard_empty]
      have := hS ∅ ∅ (by simp)
      simpa using this)

/-- A promise-enforcing additive sweep pays the original input count, regardless
of the number of supplied values. Constructing a cheap such sweep is a separate
circuit supply obligation. -/
theorem AdditiveSweep.ncard_le_inputGraph [AddMonoid G] [AddCancelMonoid H]
    [Finite G] [Finite H] {S : Set G} {K : ℕ} (p : G → H)
    (P : AdditiveSweep (inputGraph p S) M) (hS : SumsetFree S K)
    (hK1 : 1 < K) (hK : K ≤ S.ncard) :
    S.ncard ≤ (K - 1) ^ 2 * P.transitionCount := by
  simpa using P.ncard_le (hS.inputGraph p) hK1 (by simpa using hK)

/-- An injective additive change of coordinates preserves sumset dispersion. -/
theorem SumsetDisperser.comp_addHom {ι κ U : Type*} [AddMonoid U]
    {f : (ι → U) → Bool} {K : ℕ} (hf : SumsetDisperser f K)
    (e : (κ → U) →+ (ι → U)) (he : Function.Injective e) :
    SumsetDisperser (fun x => f (e x)) K := by
  intro A B hA hB b
  obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, h⟩ :=
    hf (e '' A) (e '' B)
      (by rwa [ncard_image_of_injective _ he])
      (by rwa [ncard_image_of_injective _ he]) b
  exact ⟨x, hx, y, hy, by simpa using h⟩

universe u v

/-- Free independent parity inputs preserve the full coefficient: an invertible
additive basis can be changed without building a parity circuit. The number of
supplied inputs here is exactly the original dimension; redundant inputs are not
covered by this theorem. -/
theorem lowerBound_sumsetDisperser_freeBasis {U : Type u} [AddMonoid U]
    [Finite U] [Nontrivial U] (f : ∀ n, (Fin n → U) → Bool) (K : ℕ → ℕ)
    (hf : ∀ᶠ n in atTop, SumsetDisperser (f n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    {δ : ℝ} (hδ : 0 < δ)
    (hbal : ∀ᶠ n in atTop, δ * (Nat.card U : ℝ) ^ n ≤ {x | f n x = true}.ncard)
    (e : ∀ n, (Fin n → U) ≃+ (Fin n → U)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 →
      (∀ x, c.eval I (e n x) 0 ∈ Acc ↔ f n x = true) →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n <
          c.innerSize := by
  let g := fun n x => f n ((e n).symm x)
  have hg : ∀ᶠ n in atTop, SumsetDisperser (g n) (K n) :=
    hf.mono fun n hn => hn.comp_addHom (e n).symm.toAddMonoidHom (e n).symm.injective
  have hcard : ∀ n, {x | g n x = true}.ncard = {x | f n x = true}.ncard := by
    intro n
    have hset : {x | g n x = true} = e n '' {x | f n x = true} := by
      ext x
      constructor
      · intro hx
        exact ⟨(e n).symm x, hx, (e n).apply_symm_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa [g] using hy
    rw [hset, ncard_image_of_injective _ (e n).injective]
  have hgbal : ∀ᶠ n in atTop, δ * (Nat.card U : ℝ) ^ n ≤ {x | g n x = true}.ncard := by
    simpa only [hcard] using hbal
  filter_upwards [lowerBound_sumsetDisperser g K hg hK hδ hgbal hε] with n hn
  intro σ I Acc c hfan hc
  apply hn σ I Acc c hfan
  intro x
  simpa [g] using (hc ((e n).symm x)).symm

end Frontier

namespace Frontier

open Set

variable {ι κ F : Type*} [Field F] (L : (ι → F) →ₗ[F] (κ → F))

/-- The physical circuit input contains the original values and the supplied parities. -/
def parityInput (x : ι → F) : (ι ⊕ κ) → F := Sum.elim x (L x)

theorem parityInput_injective : Function.Injective (parityInput L) := by
  intro x y h
  funext i
  exact congrFun h (.inl i)

/-- The linear embedding whose coordinates are the original and supplied values. -/
def parityInputMap : (ι → F) →ₗ[F] ((ι ⊕ κ) → F) :=
  (LinearEquiv.sumArrowLequivProdArrow ι κ F F).symm.toLinearMap.comp
    (LinearMap.id.prod L)

@[simp] theorem parityInputMap_apply (x : ι → F) : parityInputMap L x = parityInput L x := rfl

theorem finrank_parityInputMap [Finite ι] :
    Module.finrank F (LinearMap.range (parityInputMap L)) = Nat.card ι := by
  let _ := Fintype.ofFinite ι
  rw [LinearMap.finrank_range_of_inj (parityInput_injective L), Module.finrank_pi,
    Nat.card_eq_fintype_card]

/-- The zero syndrome means that every supplied parity is consistent with the
original input. Away from this fiber a promised circuit may behave arbitrarily. -/
def parityCheck : ((ι ⊕ κ) → F) →ₗ[F] (κ → F) where
  toFun z := (fun j => z (.inr j)) - L (fun i => z (.inl i))
  map_add' x y := by
    change ((fun j => x (.inr j)) + (fun j => y (.inr j))) -
      L ((fun i => x (.inl i)) + (fun i => y (.inl i))) = _
    rw [L.map_add]
    abel
  map_smul' a x := by
    change a • (fun j => x (.inr j)) - L (a • fun i => x (.inl i)) = _
    rw [L.map_smul, smul_sub]
    rfl

@[simp] theorem parityCheck_parityInput (x : ι → F) : parityCheck L (parityInput L x) = 0 := by
  simp [parityCheck, parityInput]

theorem parityCheck_eq_zero_iff (z : (ι ⊕ κ) → F) :
    parityCheck L z = 0 ↔ z = parityInput L (fun i => z (.inl i)) := by
  change (fun j => z (.inr j)) - L (fun i => z (.inl i)) = 0 ↔ _
  rw [sub_eq_zero]
  constructor
  · intro h
    funext i
    cases i with
    | inl i => rfl
    | inr j => exact congrFun h j
  · intro h
    funext j
    exact congrFun h (.inr j)

theorem parityCheck_surjective : Function.Surjective (parityCheck L) := by
  intro y
  refine ⟨Sum.elim (fun _ => 0) y, ?_⟩
  change y - L 0 = y
  rw [map_zero, sub_zero]

/-- The parity checks define exactly the supplied input code. -/
theorem ker_parityCheck :
    LinearMap.ker (parityCheck L) = LinearMap.range (parityInputMap L) := by
  ext z
  rw [LinearMap.mem_ker, parityCheck_eq_zero_iff]
  constructor
  · intro h
    exact ⟨fun i => z (.inl i), h.symm⟩
  · rintro ⟨x, rfl⟩
    rfl

/-- On consistent inputs, the ambient accepting set is exactly the lifted hard
set. No behavior of the circuit on inconsistent inputs is constrained. -/
theorem inter_parityCheck_eq {S : Set (ι → F)} {T : Set ((ι ⊕ κ) → F)}
    (hT : ∀ x, parityInput L x ∈ T ↔ x ∈ S) :
    T ∩ (parityCheck L) ⁻¹' {0} = parityInput L '' S := by
  ext z
  constructor
  · rintro ⟨hz, hc⟩
    have heq := (parityCheck_eq_zero_iff L z).mp hc
    refine ⟨(fun i => z (.inl i)), (hT _).mp ?_, heq.symm⟩
    rwa [← heq]
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(hT x).mpr hx, parityCheck_parityInput L x⟩

/-- The consistency-enforcing sweep has the original input demand. Its transition
count must still be bounded by a separate supply argument. -/
theorem ncard_le_parity_restrict [Finite ι] [Finite κ] [Finite F] {M : Type*}
    {S : Set (ι → F)} {T : Set ((ι ⊕ κ) → F)} {K : ℕ}
    (hS : SumsetFree S K) (hK : K ≤ S.ncard)
    (hT : ∀ x, parityInput L x ∈ T ↔ x ∈ S) (P : Sweep T M) :
    S.ncard ≤ (K - 1) ^ 2 *
      (P.restrictHom (parityCheck L).toAddMonoidHom 0).transitionCount := by
  let e := LinearEquiv.sumArrowLequivProdArrow ι κ F F
  have hset : parityInput L '' S = e ⁻¹' inputGraph L S := by
    ext z
    rw [mem_preimage, mem_inputGraph]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, rfl⟩
    · rintro ⟨hx, hc⟩
      refine ⟨(fun i => z (.inl i)), hx, ?_⟩
      funext i
      cases i with
      | inl i => rfl
      | inr j => exact (congrFun hc j).symm
  have hfree : SumsetFree (T ∩ (parityCheck L) ⁻¹' {0}) K := by
    rw [inter_parityCheck_eq L hT, hset]
    exact (hS.inputGraph L).preimage_addEquiv e.toAddEquiv
  have hcard : (T ∩ (parityCheck L) ⁻¹' {0}).ncard = S.ncard := by
    rw [inter_parityCheck_eq L hT, ncard_image_of_injective _ (parityInput_injective L)]
  have hbound := (P.restrictHom (parityCheck L).toAddMonoidHom 0).ncard_le
    hfree.rectangleFree (by change K ≤ (T ∩ (parityCheck L) ⁻¹' {0}).ncard; rwa [hcard])
  change (T ∩ (parityCheck L) ⁻¹' {0}).ncard ≤ (K - 1) ^ 2 *
    (P.restrictHom (parityCheck L).toAddMonoidHom 0).transitionCount at hbound
  rwa [hcard] at hbound

/-- Redundant linear inputs preserve the exact frontier demand. A sweep of the
ambient accepting set can enforce consistency at a cost of at most one syndrome
per transition. The factor `q^|κ|` is retained explicitly. -/
theorem ncard_le_parity_sweep [Finite ι] [Finite κ] [Finite F] {M : Type*}
    {S : Set (ι → F)} {T : Set ((ι ⊕ κ) → F)} {K : ℕ}
    (hS : SumsetFree S K) (hK : K ≤ S.ncard)
    (hT : ∀ x, parityInput L x ∈ T ↔ x ∈ S) (P : Sweep T M)
    (hmono : ∀ t < P.length, P.revealed t ⊆ P.revealed (t + 1)) :
    S.ncard ≤ (K - 1) ^ 2 * Nat.card F ^ Nat.card κ * P.transitionCount := by
  have hsupply := P.transitionCount_restrictHom_le (parityCheck L).toAddMonoidHom 0 hmono
  have hrange : (range (parityCheck L).toAddMonoidHom).ncard =
      Nat.card F ^ Nat.card κ := by
    rw [show range (parityCheck L).toAddMonoidHom = univ from
      (parityCheck_surjective L).range_eq, ncard_univ, Nat.card_fun]
  rw [hrange] at hsupply
  exact (ncard_le_parity_restrict L hS hK hT P).trans
    (by simpa only [mul_assoc] using Nat.mul_le_mul_left ((K - 1) ^ 2) hsupply)

/-- Joint supply for free parity inputs: count visible supplied values and the
partial syndrome once. All code hypotheses concern consistent accepting inputs;
the independent dimension in the exponent is the original input count. -/
theorem ncard_le_parity_joint_codes [Finite ι] [Finite κ] [Finite F] {M : Type*}
    {S : Set (ι → F)} {T : Set ((ι ⊕ κ) → F)} {K : ℕ}
    (hS : SumsetFree S K) (hK : K ≤ S.ncard)
    (hT : ∀ x, parityInput L x ∈ T ↔ x ∈ S) (P : Sweep T M)
    (hmono : ∀ t < P.length, P.revealed t ⊆ P.revealed (t + 1))
    (Q : ℕ → Set (ι ⊕ κ)) {D : ℕ → Type*}
    (code : ∀ t, ((ι ⊕ κ) → F) → D t) (C : ∀ t, Set (D t))
    (hC : ∀ t < P.length, (C t).Finite)
    (hmem : ∀ t < P.length, ∀ x ∈ S, code t (parityInput L x) ∈ C t)
    (hdet : ∀ t < P.length, ∀ x ∈ S, ∀ y ∈ S,
      code t (parityInput L x) = code t (parityInput L y) →
      LinearBoundary.coordinateMap (parityInputMap L) (Q t) x =
        LinearBoundary.coordinateMap (parityInputMap L) (Q t) y →
          P.transition t (parityInput L x) = P.transition t (parityInput L y)) :
    S.ncard ≤ (K - 1) ^ 2 * ∑ t ∈ Finset.range P.length, (C t).ncard *
      Nat.card F ^ (Module.finrank F (LinearMap.range
        (LinearBoundary.coordinateMap (parityInputMap L) (P.revealed t ∪ Q t))) +
        Module.finrank F (LinearMap.range
          (LinearBoundary.coordinateMap (parityInputMap L) ((P.revealed t)ᶜ ∪ Q t))) -
            Nat.card ι) := by
  have h := P.transitionCount_restrictLinear_le_joint (parityInputMap L) (parityCheck L)
    (ker_parityCheck L) hmono Q code C hC (by
      rintro t ht _ ⟨hx, x, rfl⟩
      exact hmem t ht x ((hT x).mp hx)) (by
      rintro t ht _ ⟨hx, x, rfl⟩ _ ⟨hy, y, rfl⟩ hc hq
      exact hdet t ht x ((hT x).mp hx) y ((hT y).mp hy) hc hq)
  rw [finrank_parityInputMap] at h
  exact (ncard_le_parity_restrict L hS hK hT P).trans
    (Nat.mul_le_mul_left ((K - 1) ^ 2) h)

end Frontier
