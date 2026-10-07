/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Arithmetic.Compiler
public import Frontier.Layouts
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Tactic

/-!
# Arithmetic lower bounds from mixed-Hessian demand

The demand is a property of the output polynomial and its input orders, independent
of the circuit. The point of evaluation may depend on the order and its cut. All
variables must occur formally in the output, so the compiler reads every input.
Only one output is used; its compiled graph is connected automatically.
-/

@[expose] public section

namespace Frontier.Arithmetic

open Cslib.Circuits Set MvPolynomial Filter

universe u v

variable {F : Type u} [Field F] {n s : ℕ}

/-- Every input order has a prefix and an evaluation point with mixed rank at least `d`.
Injective positions allow gaps, so the same definition applies to circuit layouts. -/
def HessianDemand (f : MvPolynomial (Fin n) F) (d : ℝ) : Prop :=
  ∀ pos : Fin n ↪ ℕ, ∃ (t : ℕ) (a : Fin n → F), d ≤
    (mixedRank f a {i | pos i < t} : ℝ)

variable {σ : Signature.{v}} (P : (o : σ.Op) → MvPolynomial (Fin (σ.Arity o)) F)
  (p : Program σ n s) (out : Unit → Wire n s)

/-- Formal dependence on every variable makes every input reachable. -/
theorem read_of_vars (hvars : ∀ i, i ∈ (wirePolynomial P p (out ())).vars) :
    ∀ i, Compiler.Reach p out (.input i) :=
  fun i => Compiler.reach_of_upstream (upstream_of_mem_vars P p i _ (hvars i))

/-- Input-order Hessian demand gives demand on every layout of the compiled graph. -/
theorem exists_cut_of_hessianDemand {d : ℝ}
    (hd : HessianDemand (wirePolynomial P p (out ())) d)
    (hread : ∀ i, Compiler.Reach p out (.input i))
    (π : Layout (Compiler.Vertex p out)) :
    ∃ t, d ≤ (((Compiler.network p out (polynomialInterpretation P F) fun _ => univ).cut
      (π.initial t)).ncard : ℝ) := by
  let input : Fin n ↪ Compiler.Vertex p out :=
    ⟨fun i => .signal ⟨.input i, hread i⟩, by intro i j h; simpa using h⟩
  let pos := input.trans (π.toEmbedding.trans Fin.valEmbedding)
  obtain ⟨t, a, ht⟩ := hd pos
  have hS : {i | pos i < t} =
      (Compiler.network p out (polynomialInterpretation P F) fun _ => univ).readIn
        (π.initial t) := by
    ext i
    constructor
    · intro hi
      exact ⟨.signal ⟨.input i, hread i⟩, hi, Compiler.site_of_reach (hread i)⟩
    · rintro ⟨w, hw, hiw⟩
      obtain ⟨_, rfl⟩ := Compiler.site_eq_some hiw
      exact hw
  rw [hS] at ht
  classical
  rw [mixedRank_eq] at ht
  exact ⟨t, ht.trans (by exact_mod_cast rank_mixedHessian_le_cut P p out (π.initial t) () a)⟩

/-- **Finite arithmetic lower-bound transfer.** The constant is uniform over fields,
gate polynomials, circuit sizes, output polynomials, and demands. Constants are free;
`p.innerGates.card` counts only gates of positive arity. -/
theorem hessian_gate_bound {A η : ℝ} (hA : 0 ≤ A) (hlayout : LayoutBound 3 A)
    (hη : 0 < η) : ∃ C : ℝ, ∀ (F : Type u) [Field F] (σ : Signature.{v})
      (P : (o : σ.Op) → MvPolynomial (Fin (σ.Arity o)) F)
      (n s : ℕ) (p : Program σ n s) (out : Unit → Wire n s) (d : ℝ),
      p.FanInAtMost 2 → (∀ i, i ∈ (wirePolynomial P p (out ())).vars) →
      HessianDemand (wirePolynomial P p (out ())) d →
      (A + η) * n + d ≤ (A + 5 * η) * p.innerGates.card + A + 4 * η + C := by
  obtain ⟨C, hC⟩ := hlayout η hη
  refine ⟨C, ?_⟩
  intro F _ σ P n s p out d hfan hvars hd
  let N := Compiler.network p out (polynomialInterpretation P F) fun _ => univ
  have hconn := Compiler.connected (p := p) (out := out) (polynomialInterpretation P F)
    (fun _ => univ)
  obtain ⟨π, hπ⟩ := hC _ _ N.toMultigraph hconn (Compiler.loopless _ _)
    (Compiler.maxDegreeLE _ _ (by decide) hfan)
  obtain ⟨t, ht⟩ := exists_cut_of_hessianDemand P p out hd (read_of_vars P p out hvars) π
  have hsupply := ht.trans (hπ t)
  have hr := Compiler.cycleRank_add_ncard_read_le (out := out)
    (polynomialInterpretation P F) (fun _ => univ) hfan hconn
  have hread : N.read = univ := by
    rw [Compiler.read_network]
    exact eq_univ_of_forall (read_of_vars P p out hvars)
  change N.cycleRank + N.read.ncard ≤ _ at hr
  rw [hread] at hr
  simp only [ncard_univ, Nat.card_fin, Nat.reduceSub, one_mul] at hr
  have hr' : (N.cycleRank : ℝ) + n ≤ p.innerGates.card + 1 := by exact_mod_cast hr
  have hV := Compiler.card_vertex_le (out := out) hfan
  have hV' : (Nat.card (Compiler.Vertex p out) : ℝ) ≤ 4 * p.innerGates.card + 3 := by
    norm_num at hV
    exact_mod_cast hV
  have h1 := mul_le_mul_of_nonneg_left hr' (by positivity : 0 ≤ A + η)
  have h2 := mul_le_mul_of_nonneg_left hV' hη.le
  dsimp only [N] at hr' h1
  linarith

/-- **Asymptotic arithmetic lower bound.** Linear mixed-Hessian demand `ρ n` yields
the coefficient `1 + ρ / A`, uniformly over arbitrary fields and polynomial bases. -/
theorem lowerBound_hessian {A ρ : ℝ} (hA : 0 < A) (hρ : 0 ≤ ρ)
    (hlayout : LayoutBound 3 A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (F : Type u) [Field F] (σ : Signature.{v})
      (P : (o : σ.Op) → MvPolynomial (Fin (σ.Arity o)) F)
      (s : ℕ) (p : Program σ n s) (out : Unit → Wire n s),
      p.FanInAtMost 2 → (∀ i, i ∈ (wirePolynomial P p (out ())).vars) →
      HessianDemand (wirePolynomial P p (out ())) (ρ * n) →
      (1 + ρ / A - ε) * n < p.innerGates.card := by
  let K := 1 + ρ / A
  have hK : 0 < K := by dsimp [K]; positivity
  have hKA : A * K = A + ρ := by dsimp [K]; field_simp
  let η := ε * A / (10 * (K + 1))
  have hη : 0 < η := by positivity
  have hηeq : 10 * (K + 1) * η = ε * A := by
    dsimp [η]
    field_simp
  let δ := A + η + ρ - (A + 5 * η) * (K - ε)
  have hδ : 0 < δ := by dsimp [δ]; nlinarith
  obtain ⟨C, hC⟩ := hessian_gate_bound.{u, v} hA.le hlayout hη
  have hlarge : ∀ᶠ n : ℕ in atTop, (A + 4 * η + C) / δ < (n : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop _)
  filter_upwards [hlarge] with n hn
  intro F _ σ P s p out hfan hvars hd
  have hb := hC F σ P n s p out (ρ * n) hfan hvars hd
  have hconst : A + 4 * η + C < δ * n := by
    simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hn
  by_contra! hs
  have hmul := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ A + 5 * η)
  change (p.innerGates.card : ℝ) ≤ (K - ε) * n at hs
  change (A + 5 * η) * p.innerGates.card ≤ (A + 5 * η) * ((K - ε) * n) at hmul
  dsimp only [δ] at hconst
  nlinarith

/-- Instantiate the scalar-polynomial transfer with the checked Gaussian layout theorem. -/
theorem lowerBound_hessian_gaussian {ρ : ℝ} (hρ : 0 ≤ ρ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (F : Type u) [Field F] (σ : Signature.{v})
      (P : (o : σ.Op) → MvPolynomial (Fin (σ.Arity o)) F)
      (s : ℕ) (p : Program σ n s) (out : Unit → Wire n s),
      p.FanInAtMost 2 → (∀ i, i ∈ (wirePolynomial P p (out ())).vars) →
      HessianDemand (wirePolynomial P p (out ())) (ρ * n) →
      (1 + ρ / (2 * Gaussian.gaussianCoefficient) - ε) * n < p.innerGates.card :=
  lowerBound_hessian (by positivity [Gaussian.gaussianCoefficient_pos]) hρ
    layoutBound_gaussian hε

end Frontier.Arithmetic
