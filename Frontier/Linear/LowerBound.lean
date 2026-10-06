/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Boundary.Fiber
public import Frontier.Compiler
public import Frontier.Demand
public import Frontier.Linear.TotallyRegular
public import Frontier.Linear.Linearize

/-!
# Lower bounds for linear maps

The frontier method applies to circuits with many outputs. Here the demand comes from linear
algebra instead of from counting rectangles.

Let a circuit over a field `F` compute `x ↦ M x` for an `N × N` matrix `M`, and compile it into
a network that accepts every value at every output. Cut the network along a set `P` of vertices:
`P` reads the inputs `X` and holds the outputs `Y`. If the runs on two inputs agree on the cut,
then splicing them (`Frontier.Compiler.trace_out_of_cut`) shows that the outputs in `Y` do not
see the inputs outside `X`, and the outputs outside `Y` do not see the inputs in `X`. When `M` is
totally regular and `|X| + |Y| = N`, both blocks `M[Y, X^c]` and `M[Y^c, X]` are square and
nonsingular: the map is MDS (`Frontier.TotallyRegular.isMDS`), so the input is determined by
the values on the cut (`Frontier.exists_injective_cut`, from the mixed-fiber splicing of
`Frontier.Boundary.Fiber`). Every layout passes through such a `P`, since `|X| + |Y|` grows by
at most one per vertex, from `0` to `2 N`.

How many values can a cut of `k` edges carry? A circuit has *linear capacity*
(`Frontier.LinearCapacity`) when `k` wires never determine more than `k` coordinates of the
input. This holds

* over a finite field, for every basis: `k` wires take at most `|F| ^ k` values
  (`Frontier.linearCapacity_of_finite`);
* over any field, for the affine basis: the values of `k` wires are an affine function of the
  input (`Frontier.linearCapacity_affine`);
* over an infinite field, for polynomial operations, after linearizing the circuit
  (`Frontier.exists_affine_circuit`).

It fails over infinite fields for arbitrary operations: a bijection `F × F → F` lets one wire
carry everything.

So every layout of the graph of the circuit has a frontier of at least `N` edges: the demand is
exactly `N`. The graph has cycle rank at most `(r - 1) s + 1 - N` for `s` inner gates of
fan-in `r`, and the comparison of demand and supply gives the same coefficient as for decision
problems.

**Main theorem** (`Frontier.lowerBound_linear`). Under `LayoutBound (r + 1) A`, for every
`ε > 0` and all large `N`, every circuit of fan-in at most `r` with linear capacity computing a
totally regular map `F^N → F^N` has `s` inner gates with `(r - 1) s > (1 + 1/A - ε) N`, uniformly
in the field. Constants are free.

## Main results

* `Frontier.exists_injective_cut`: some frontier of every layout determines the input.
* `Frontier.lowerBound_of_exact_demand`: the demand-and-supply comparison for an exact demand
  of `N`, shared with the nonlinear MDS bound.
* `Frontier.lowerBound_linear`: the lower bound, for circuits with linear capacity.
* `Frontier.lowerBound_linear_finite`, `Frontier.lowerBound_linear_affine`,
  `Frontier.lowerBound_linear_polynomial`: over finite fields with any basis, over any field with
  the affine basis, and over infinite fields with polynomial operations.
-/

@[expose] public section

namespace Frontier

open Cslib.Circuits Set Filter Asymptotics Matrix

universe u v

/-! ### Linear capacity -/

section Capacity

variable {F : Type u} [Field F] {σ : Signature.{v}} {N m : ℕ}

/-- A circuit has *linear capacity* when its wires carry at most one element of the field each:
whenever the values of `k` wires determine the input, `N ≤ k`. -/
def LinearCapacity (I : Interpretation σ F) (c : Circuit σ N m) : Prop :=
  ∀ (T : Type) [Finite T] (w : T → Wire N c.size),
    Function.Injective (fun x : Fin N → F => fun t => c.program.trace I x (w t)) →
      N ≤ Nat.card T

/-- Over a finite field every circuit has linear capacity: `k` wires take at most `|F| ^ k`
values. -/
theorem linearCapacity_of_finite [Finite F] (I : Interpretation σ F) (c : Circuit σ N m) :
    LinearCapacity I c := by
  intro T _ w hw
  have h := Nat.card_le_card_of_injective _ hw
  rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin N), Fintype.card_fin] at h
  exact (Nat.pow_le_pow_iff_right Finite.one_lt_card).mp h

/-- Circuits over the affine basis have linear capacity: the values of `k` wires are an affine
function of the input, which is injective only if `N ≤ k`. -/
theorem linearCapacity_affine (c : Circuit (affineSignature F) N m) :
    LinearCapacity (affineInterpretation F) c := by
  intro T _ w hw
  have := Fintype.ofFinite T
  choose L b hL using fun t => exists_affine_trace c.program (w t)
  let Φ : (Fin N → F) →ₗ[F] (T → F) := LinearMap.pi L
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    refine hw (funext fun t => ?_)
    have := congrFun hxy t
    simp only [LinearMap.pi_apply, Φ] at this
    simp only [hL, this]
  have := LinearMap.finrank_le_finrank_of_injective hΦ
  simpa [Nat.card_eq_fintype_card] using this

end Capacity

/-! ### Every layout has a frontier that determines the input -/

/-- Total regularity is the linear special case of mixed recovery. -/
theorem TotallyRegular.isMDS {N : ℕ} {K : Type*} [Field K]
    {M : Matrix (Fin N) (Fin N) K} (hM : TotallyRegular M) :
    IsMDS (fun x => M *ᵥ x) := by
  classical
  intro X Y hXY x y hX hY
  have hXc := ncard_add_ncard_compl X
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hXc
  have H := hM.eq_zero (R := Y.toFinset) (C := Xᶜ.toFinset) (v := x - y)
    (by simpa only [← ncard_eq_toFinset_card'] using (by omega : Y.ncard = Xᶜ.ncard))
    (fun j hj => by
      have hj : j ∈ X := by simpa using hj
      simp [hX hj])
    (fun i hi => by
      have hi : i ∈ Y := by simpa using hi
      simp only [Matrix.mulVec_sub, Pi.sub_apply, hY hi, sub_self])
  exact sub_eq_zero.mp H

section Graph

variable {F : Type u} [Field F] {σ : Signature.{v}} {I : Interpretation σ F} {N : ℕ}
  {M : Matrix (Fin N) (Fin N) F} {c : Circuit σ N N}

/-- The network of a circuit computing a function: every value is accepted at every output. -/
noncomputable abbrev functionNetwork (I : Interpretation σ F) (c : Circuit σ N N) :=
  Compiler.network c.program c.outputs I fun _ => univ

/-- **Every output of a totally regular map depends on every input**, so every input is
upstream of every output. -/
theorem upstream_of_totallyRegular (hM : TotallyRegular M) (hc : c.Computes I fun x => M *ᵥ x)
    (o i : Fin N) : c.program.Upstream (c.outputs o) (.input i) :=
  upstream_of_mds hM.isMDS hc o i

/-- **Some frontier of every layout determines the input.** For a circuit computing a totally
regular map, every layout of its network has a time at which the values on the frontier
determine the input. -/
theorem exists_injective_cut (hM : TotallyRegular M) (hc : c.Computes I fun x => M *ᵥ x)
    (π : Layout (Compiler.Vertex c.program c.outputs)) :
    ∃ t, Function.Injective fun (x : Fin N → F)
      (e : ↥((functionNetwork I c).cut (π.initial t))) => c.program.trace I x e.1.signal.1 :=
  exists_injective_cut_mds hM.isMDS hc π

/-- **The graph of a circuit for a totally regular map.** A circuit with `s` inner gates of
fan-in at most `r ≥ 2` and linear capacity, computing a totally regular map `F^N → F^N` with
`N ≥ 1`, yields a connected, loopless multigraph of maximum degree `r + 1` with at most
`2 r s + 3 N` vertices and cycle rank at most `(r - 1) s + 1 - N`, every layout of which has a
frontier of at least `N` edges. -/
theorem exists_graph_of_totallyRegular (hN : 1 ≤ N) {r : ℕ} (hr : 2 ≤ r)
    (hfan : c.FanInAtMost r) (hM : TotallyRegular M) (hc : c.Computes I fun x => M *ᵥ x)
    (hcap : LinearCapacity I c) :
    ∃ (V E : Type) (_ : Finite V) (_ : Finite E) (G : Multigraph V E),
      G.Connected ∧ G.Loopless ∧ G.MaxDegreeLE (r + 1) ∧
      Nat.card V ≤ 2 * r * c.innerSize + 3 * N ∧
      G.cycleRank + N ≤ (r - 1) * c.innerSize + 1 ∧
      ∀ π : Layout V, ∃ t, N ≤ (G.cut (π.initial t)).ncard :=
  exists_graph_of_upstream hN hr hfan (upstream_of_totallyRegular hM hc) fun π => by
    obtain ⟨t, ht⟩ := exists_injective_cut hM hc π
    exact ⟨t, (hcap _ (fun e => e.1.signal.1) ht).trans_eq (Nat.card_coe_set_eq _)⟩

end Graph

/-! ### The lower bound -/

/-- **Demand and supply for an exact demand.** A graph with the shape and size of a compiled
circuit for an `N`-input, `N`-output map, every layout of which has a frontier of at least `N`
edges, has `(r - 1) s > (1 + 1/A - ε) N` for all large `N`, where `s` is its gate budget. -/
theorem lowerBound_of_exact_demand {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (gates : ℕ) (V E : Type) [Finite V] [Finite E] (G : Multigraph V E),
      G.Connected → G.Loopless → G.MaxDegreeLE (r + 1) →
      Nat.card V ≤ 2 * r * gates + 3 * N →
      G.cycleRank + N ≤ (r - 1) * gates + 1 →
      (∀ π : Layout V, ∃ t, N ≤ (G.cut (π.initial t)).ncard) →
      (1 + 1 / A - ε) * N < (r - 1) * gates := by
  obtain ⟨η, hη, H⟩ := eventually_lt_of_demand hA (κ := 4) (by norm_num) hε
  obtain ⟨C, hC⟩ := hlayout η hη
  replace H := H η hη le_rfl
  filter_upwards [H C (fun _ => 1) (isLittleO_const_left.mpr
      (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop)))] with N hN
  intro gates V E _ _ G hconn hloop hdeg hV hrank hwidth
  obtain ⟨π, hπ⟩ := hC V E G hconn hloop hdeg
  set B := (A + η) * G.cycleRank + η * Nat.card V + C
  obtain ⟨t, ht⟩ := hwidth π
  have hB : (N : ℝ) ≤ B := (by exact_mod_cast ht : (N : ℝ) ≤ _).trans (hπ t)
  set s : ℝ := (((r - 1) * gates : ℕ) : ℝ)
  have hs : s = (r - 1) * gates := by
    simp only [s]; rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
  have hVs : (Nat.card V : ℝ) ≤ 4 * (N + s + 1) := by
    have : 2 * r * gates + 3 * N ≤ 4 * ((r - 1) * gates) + 4 * N := by
      have : 2 * r ≤ 4 * (r - 1) := by omega
      nlinarith
    have h4 : (Nat.card V : ℝ) ≤ 4 * ((r - 1) * gates : ℕ) + 4 * N := by
      exact_mod_cast hV.trans this
    simp only [s]
    linarith
  rw [← hs]
  refine hN s (Nat.card V) B (Nat.cast_nonneg _) (Nat.cast_nonneg _) hVs ?_ ?_
  · have : 0 ≤ Real.log (Nat.card V + 1) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (Nat.card V)])
    linarith
  · have hrank' : (G.cycleRank : ℝ) ≤ s - N + 1 := by
      have : (G.cycleRank : ℝ) + N ≤ ((r - 1) * gates : ℕ) + 1 := by exact_mod_cast hrank
      simp only [s]; linarith
    have := mul_le_mul_of_nonneg_left hrank' (by linarith : 0 ≤ A + η)
    linarith

/-- **The frontier lower bound for linear maps.** Let `r ≥ 2` and assume the layout hypothesis
for maximum degree `r + 1` with coefficient `A > 0`. For every `ε > 0` and all large `N`, every
circuit of fan-in at most `r` with linear capacity, over any field and any basis, that computes
`x ↦ M x` for a totally regular `N × N` matrix `M`, has `s` inner gates with
`(r - 1) s > (1 + 1/A - ε) N`. -/
theorem lowerBound_linear {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] (σ : Signature.{v}) (I : Interpretation σ F)
      (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N), TotallyRegular M →
        c.FanInAtMost r → c.Computes I (fun x => M *ᵥ x) → LinearCapacity I c →
          (1 + 1 / A - ε) * N < (r - 1) * c.innerSize := by
  filter_upwards [lowerBound_of_exact_demand hr hA hlayout hε, eventually_ge_atTop 1]
    with N hN hN1
  intro F _ σ I M c hM hfan hc hcap
  obtain ⟨V, E, _, _, G, hconn, hloop, hdeg, hV, hrank, hwidth⟩ :=
    exists_graph_of_totallyRegular hN1 hr hfan hM hc hcap
  exact hN c.innerSize V E G hconn hloop hdeg hV hrank hwidth

/-- **Linear maps over finite fields**, over any basis. -/
theorem lowerBound_linear_finite {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Finite F] (σ : Signature.{v})
      (I : Interpretation σ F) (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N),
        TotallyRegular M → c.FanInAtMost r → c.Computes I (fun x => M *ᵥ x) →
          (1 + 1 / A - ε) * N < (r - 1) * c.innerSize := by
  filter_upwards [lowerBound_linear.{u, v} hr hA hlayout hε] with N hN
  intro F _ _ σ I M c hM hfan hc
  exact hN F σ I M c hM hfan hc (linearCapacity_of_finite I c)

/-- **Linear maps over any field**, over the affine basis. -/
theorem lowerBound_linear_affine {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] (M : Matrix (Fin N) (Fin N) F)
      (c : Circuit (affineSignature F) N N), TotallyRegular M → c.FanInAtMost r →
        c.Computes (affineInterpretation F) (fun x => M *ᵥ x) →
          (1 + 1 / A - ε) * N < (r - 1) * c.innerSize := by
  filter_upwards [lowerBound_linear.{u, u} hr hA hlayout hε] with N hN
  intro F _ M c hM hfan hc
  exact hN F _ _ M c hM hfan hc (linearCapacity_affine c)

/-- **Linear maps over infinite fields**, over any basis of polynomial operations: the
coefficients and degrees of the operations are arbitrary. -/
theorem lowerBound_linear_polynomial {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Infinite F] (σ : Signature.{v})
      (I : Interpretation σ F), IsPolynomial I → ∀ (M : Matrix (Fin N) (Fin N) F)
        (c : Circuit σ N N), TotallyRegular M → c.FanInAtMost r →
          c.Computes I (fun x => M *ᵥ x) → (1 + 1 / A - ε) * N < (r - 1) * c.innerSize := by
  filter_upwards [lowerBound_linear_affine.{u} hr hA hlayout hε] with N hN
  intro F _ _ σ I hI M c hM hfan hc
  obtain ⟨c', -, hinner, hfan', hc'⟩ := exists_affine_circuit hI c M hc
  rw [← hinner]
  exact hN F M c' hM (hfan' r hfan) hc'

end Frontier
