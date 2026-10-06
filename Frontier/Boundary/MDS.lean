/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Boundary.Fiber
public import Frontier.Linear.LowerBound
public import Frontier.Layouts

/-!
# Nonlinear recovery maps

The graph code `(x, F x)` is MDS when any `N` of its `2N` coordinates determine `x`
(`Frontier.IsMDS`). Every layout has a cut containing exactly `N` input and output terminals,
and the complementary mixed observations at that cut are both injective, so its signal values
determine the input (`Frontier.exists_injective_cut_mds`). Over a finite alphabet this gives
the same circuit lower bound as total regularity, through the same demand-and-supply
comparison (`Frontier.lowerBound_of_exact_demand`).
-/

@[expose] public section

namespace Frontier

open Cslib.Circuits Set Filter Asymptotics Matrix

universe u v

variable {U : Type u} {N : ℕ} {σ : Signature.{v}} {I : Interpretation σ U} {c : Circuit σ N N}
  {F : (Fin N → U) → (Fin N → U)}

/-- An MDS map supplies the same full-entropy graph demand as a totally regular matrix. -/
theorem exists_graph_of_mds [Finite U] [Nontrivial U] (hN : 1 ≤ N) {r : ℕ} (hr : 2 ≤ r)
    (hfan : c.FanInAtMost r) (hF : IsMDS F) (hc : c.Computes I F) :
    ∃ (V E : Type) (_ : Finite V) (_ : Finite E) (G : Multigraph V E),
      G.Connected ∧ G.Loopless ∧ G.MaxDegreeLE (r + 1) ∧
      Nat.card V ≤ 2 * r * c.innerSize + 3 * N ∧
      G.cycleRank + N ≤ (r - 1) * c.innerSize + 1 ∧
      ∀ π : Layout V, ∃ t, N ≤ (G.cut (π.initial t)).ncard :=
  exists_graph_of_upstream hN hr hfan (fun o i => upstream_of_mds hF hc o i) fun π => by
    obtain ⟨t, hinj⟩ := exists_injective_cut_mds hF hc π
    have H := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin N),
      Fintype.card_fin, Nat.card_coe_set_eq] at H
    exact ⟨t, (Nat.pow_le_pow_iff_right Finite.one_lt_card).mp H⟩

/-- **Circuit lower bounds from mixed recovery.** The alphabet and circuit basis are
arbitrary; finiteness supplies the capacity bound. -/
theorem lowerBound_mds {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (U : Type u) [Finite U] [Nontrivial U]
      (σ : Signature.{v}) (I : Interpretation σ U) (F : (Fin N → U) → (Fin N → U))
      (c : Circuit σ N N), IsMDS F → c.FanInAtMost r → c.Computes I F →
        (1 + 1 / A - ε) * N < (r - 1) * c.innerSize := by
  filter_upwards [lowerBound_of_exact_demand hr hA hlayout hε, eventually_ge_atTop 1]
    with N hN hN1
  intro U _ _ σ I F c hF hfan hc
  obtain ⟨V, E, _, _, G, hconn, hloop, hdeg, hV, hrank, hwidth⟩ :=
    exists_graph_of_mds hN1 hr hfan hF hc
  exact hN c.innerSize V E G hconn hloop hdeg hV hrank hwidth

/-- Nonlinear MDS maps inherit the binary Gaussian coefficient. -/
theorem mds_gaussian {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (U : Type u) [Finite U] [Nontrivial U]
      (σ : Signature.{v}) (I : Interpretation σ U) (F : (Fin N → U) → (Fin N → U))
      (c : Circuit σ N N), IsMDS F → c.FanInAtMost 2 → c.Computes I F →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * N <
          c.innerSize := by
  filter_upwards [lowerBound_mds.{u, v} le_rfl
    (mul_pos two_pos Gaussian.gaussianCoefficient_pos) layoutBound_gaussian hε] with N hN
  intro U _ _ σ I F c hF hfan hc
  have H := hN U σ I F c hF hfan hc
  rw [Gaussian.one_add_inv_two_mul_gaussianCoefficient] at H
  norm_num at H
  exact H

/-- **Every fixed fan-in for nonlinear MDS maps**, with the Gaussian degree coefficient. -/
theorem mds_degree {r : ℕ} (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (U : Type u) [Finite U] [Nontrivial U]
      (σ : Signature.{v}) (I : Interpretation σ U) (F : (Fin N → U) → (Fin N → U))
      (c : Circuit σ N N), IsMDS F → c.FanInAtMost r → c.Computes I F →
        (1 + 1 / Gaussian.degreeCoefficient (r + 1) - ε) * N <
          (r - 1) * c.innerSize :=
  lowerBound_mds hr (Gaussian.degreeCoefficient_pos (by lia)) (layoutBound_degree (by lia)) hε

end Frontier
