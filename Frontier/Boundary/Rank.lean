/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Boundary.Fiber
public import Frontier.Boundary.Linear
public import Mathlib.LinearAlgebra.Pi

/-!
# Graded demand from linear observation ranks

The systematic graph code `x ↦ (x, L x)` has a rank function on mixed input-output
observations. Its connectivity is the sum of the two complementary ranks minus the
input dimension, using Kashyap's convention without an additional `1`. Every exact
splicing code needs at least `q^connectivity` messages. In particular a circuit cut
must carry at least this many distinct field-valued signals in the exponent.
-/

@[expose] public section

namespace Frontier.LinearObservation

open Set Module

variable {F ι O M : Type*} [Field F]

/-- The linear map revealing the inputs in `X` and outputs in `Y`. -/
def observe (L : (ι → F) →ₗ[F] (O → F)) (X : Set ι) (Y : Set O) :
    (ι → F) →ₗ[F] ((X → F) × (Y → F)) where
  toFun x := (fun i => x i, fun j => L x j)
  map_add' x y := by ext <;> simp
  map_smul' a x := by ext <;> simp

/-- Rank of the corresponding rows of the systematic matrix `[I; L]`. -/
noncomputable def rank (L : (ι → F) →ₗ[F] (O → F)) (X : Set ι) (Y : Set O) : ℕ :=
  finrank F (LinearMap.range (observe L X Y))

/-- Matroid connectivity of a mixed terminal cut, with no additive convention shift. -/
noncomputable def connectivity (L : (ι → F) →ₗ[F] (O → F)) (X : Set ι) (Y : Set O) : ℕ :=
  rank L X Y + rank L Xᶜ Yᶜ - Nat.card ι

theorem observe_eq_iff (L : (ι → F) →ₗ[F] (O → F)) (X : Set ι) (Y : Set O)
    (x z : ι → F) : observe L X Y z = observe L X Y x ↔ z ∈ mixedFiber L X Y x := by
  simp only [observe, LinearMap.coe_mk, AddHom.coe_mk, Prod.mk.injEq, mixedFiber,
    mem_ofPred_eq, funext_iff, Subtype.forall, EqOn]

/-- Each nonempty mixed fiber is a translate of the observation kernel. -/
theorem mixedFiber_eq_image (L : (ι → F) →ₗ[F] (O → F)) (X : Set ι) (Y : Set O)
    (x : ι → F) : mixedFiber L X Y x =
      (fun z => z + x) '' (↑(LinearMap.ker (observe L X Y)) : Set (ι → F)) := by
  ext z
  rw [← observe_eq_iff]
  constructor
  · intro hz
    refine ⟨z - x, ?_, sub_add_cancel z x⟩
    change observe L X Y (z - x) = 0
    simp [hz]
  · rintro ⟨y, hy, rfl⟩
    change observe L X Y y = 0 at hy
    simp [hy]

/-- Exact mixed-fiber size over a finite field. All fibers have the same size. -/
theorem ncard_mixedFiber [Finite ι] [Finite F] (L : (ι → F) →ₗ[F] (O → F))
    (X : Set ι) (Y : Set O) (x : ι → F) :
    (mixedFiber L X Y x).ncard = Nat.card F ^ (Nat.card ι - rank L X Y) := by
  let := Fintype.ofFinite ι
  rw [mixedFiber_eq_image, ncard_image_of_injective _ (add_left_injective x),
    ← Nat.card_coe_set_eq]
  change Nat.card ↥(LinearMap.ker (observe L X Y)) = _
  rw [Module.natCard_eq_pow_finrank (K := F)]
  congr 1
  have H := (observe L X Y).finrank_range_add_finrank_ker
  rw [finrank_pi, ← Nat.card_eq_fintype_card] at H
  dsimp [rank]
  lia

theorem maxMixedFiber_eq [Finite ι] [Finite F] (L : (ι → F) →ₗ[F] (O → F))
    (X : Set ι) (Y : Set O) :
    maxMixedFiber L X Y = Nat.card F ^ (Nat.card ι - rank L X Y) := by
  classical
  let := Fintype.ofFinite (ι → F)
  unfold maxMixedFiber
  simp only [ncard_mixedFiber]
  exact Finset.sup_const Finset.univ_nonempty _

/-- Complementary observations together are injective, since they include every input. -/
theorem ker_inf_eq_bot (L : (ι → F) →ₗ[F] (O → F)) (X : Set ι) (Y : Set O) :
    LinearMap.ker (observe L X Y) ⊓ LinearMap.ker (observe L Xᶜ Yᶜ) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  have h1 : observe L X Y x = 0 := hx.1
  have h2 : observe L Xᶜ Yᶜ x = 0 := hx.2
  funext i
  by_cases hi : i ∈ X
  · exact congrFun (congrArg Prod.fst h1) ⟨i, hi⟩
  · exact congrFun (congrArg Prod.fst h2) ⟨i, hi⟩

/-- Connectivity plus the two kernel dimensions is exactly the input dimension. -/
theorem connectivity_add_nullities [Finite ι] (L : (ι → F) →ₗ[F] (O → F))
    (X : Set ι) (Y : Set O) :
    connectivity L X Y + ((Nat.card ι - rank L X Y) +
      (Nat.card ι - rank L Xᶜ Yᶜ)) = Nat.card ι := by
  let := Fintype.ofFinite ι
  have h1 := (observe L X Y).finrank_range_add_finrank_ker
  have h2 := (observe L Xᶜ Yᶜ).finrank_range_add_finrank_ker
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker (observe L X Y)) (LinearMap.ker (observe L Xᶜ Yᶜ))
  have h4 := Submodule.finrank_le
    (LinearMap.ker (observe L X Y) ⊔ LinearMap.ker (observe L Xᶜ Yᶜ))
  rw [ker_inf_eq_bot, finrank_bot, add_zero] at h3
  rw [finrank_pi, ← Nat.card_eq_fintype_card] at h1 h2 h4
  dsimp [connectivity, rank]
  lia

/-- **Rank demand.** Exact splicing requires `q^λ` messages at this terminal cut. -/
theorem pow_connectivity_le_messages [Finite ι] [Finite F]
    (L : (ι → F) →ₗ[F] (O → F)) (X : Set ι) (Y : Set O) (message : (ι → F) → M)
    (h : OutputSplicing L X Y message) :
    Nat.card F ^ connectivity L X Y ≤ (Set.range message).ncard := by
  have H := h.card_le
  rw [maxMixedFiber_eq, maxMixedFiber_eq, ← pow_add] at H
  have he := connectivity_add_nullities L X Y
  conv_lhs at H => rw [← he, pow_add]
  exact Nat.le_of_mul_le_mul_right H (pow_pos Nat.card_pos _)

/-- Minimum over terminal orders of their largest connectivity. Injective natural-number
positions allow gaps; removing gaps preserves exactly the same terminal cuts. -/
noncomputable def pathwidth [Finite ι] [Finite O] (L : (ι → F) →ₗ[F] (O → F)) : ℕ :=
  sInf {k | ∃ pos : (ι ⊕ O) ↪ ℕ, ∀ t,
    connectivity L {i | pos (.inl i) < t} {o | pos (.inr o) < t} ≤ k}

/-- Every terminal order attains at least the minimum possible maximum connectivity. -/
theorem exists_cut_ge_pathwidth [Finite ι] [Finite O] (L : (ι → F) →ₗ[F] (O → F))
    (pos : (ι ⊕ O) ↪ ℕ) :
    ∃ t, pathwidth L ≤ connectivity L {i | pos (.inl i) < t} {o | pos (.inr o) < t} := by
  by_cases hz : pathwidth L = 0
  · exact ⟨0, by rw [hz]; exact Nat.zero_le _⟩
  · by_contra! h
    have H : pathwidth L ≤ pathwidth L - 1 :=
      Nat.sInf_le ⟨pos, fun t => by have := h t; lia⟩
    lia

end Frontier.LinearObservation

namespace Frontier.Compiler

open Set Cslib.Circuits

variable {F O : Type*} [Field F] [Finite F] [Finite O]
  {σ : Signature} {n s : ℕ} {p : Program σ n s} {out : O → Wire n s}

/-- **Circuit cut rank demand.** A circuit computing a linear map may use arbitrary
nonlinear gates. Only its computed function, not its internal gates, is assumed linear. -/
theorem connectivity_le_cutSignals (I : Interpretation σ F)
    (L : (Fin n → F) →ₗ[F] (O → F)) (hL : ∀ x o, p.trace I x (out o) = L x o)
    (P : Set (Vertex p out)) :
    LinearObservation.connectivity L
      ((network p out I fun _ => univ).readIn P) {o | Vertex.output o ∈ P} ≤
        (cutSignals I P).ncard := by
  have h := outputSplicing I P
  simp only [hL] at h
  have H := LinearObservation.pow_connectivity_le_messages _ _ _ _ h
  apply (Nat.pow_le_pow_iff_right (show 1 < Nat.card F from Finite.one_lt_card)).mp
  exact H.trans ((ncard_le_card _).trans_eq (by rw [Nat.card_fun, Nat.card_coe_set_eq]))

/-- All reachable input sites and output sites are distinct terminals of the network. -/
def terminals (hread : ∀ i, Reach p out (.input i)) : (Fin n ⊕ O) ↪ Vertex p out where
  toFun := Sum.elim (fun i => .signal ⟨.input i, hread i⟩) .output
  inj' := by
    rintro (i | o) (j | q) h <;> simp_all

/-- **Matroid pathwidth transfer.** Every circuit layout has a signal frontier at least
as large as the systematic graph code's pathwidth. All original inputs must be reachable;
connectivity of the circuit graph is not needed for this demand theorem. -/
theorem exists_cut_ge_pathwidth (I : Interpretation σ F)
    (L : (Fin n → F) →ₗ[F] (O → F)) (hL : ∀ x o, p.trace I x (out o) = L x o)
    (hread : ∀ i, Reach p out (.input i)) (π : Layout (Vertex p out)) :
    ∃ t, LinearObservation.pathwidth L ≤ (cutSignals I (π.initial t)).ncard := by
  let pos : (Fin n ⊕ O) ↪ ℕ :=
    (terminals hread).trans (π.toEmbedding.trans Fin.valEmbedding)
  obtain ⟨t, ht⟩ := LinearObservation.exists_cut_ge_pathwidth L pos
  have hX : {i | pos (.inl i) < t} = (network p out I fun _ => univ).readIn (π.initial t) := by
    ext i
    constructor
    · intro hi
      exact ⟨.signal ⟨.input i, hread i⟩, hi, site_of_reach (hread i)⟩
    · rintro ⟨v, hv, hiv⟩
      obtain ⟨_, rfl⟩ := site_eq_some hiv
      exact hv
  rw [hX] at ht
  exact ⟨t, ht.trans (connectivity_le_cutSignals I L hL _)⟩

end Frontier.Compiler
