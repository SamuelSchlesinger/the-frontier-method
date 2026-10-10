/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.KernelPairStability
public import Frontier.Layouts.StarSupply
public import Frontier.Layouts.Pair

/-!
# The geometry of an adjacent pair in a cubic graph

The six rows used by the local covariance theorem can be chosen around every
actual edge. The other neighbors may coincide across the two stars; no girth
hypothesis is imposed. Neighbor enumerations also enumerate all three incident
edges, connecting the intrinsic star gaps to the local pair estimate.
-/

@[expose] public section

namespace Frontier.PairLayout

open Finset Gaussian

variable {V : Type} [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Order the neighbors of a cubic vertex with a prescribed neighbor first. -/
theorem exists_neighborEnum (regular : H.IsRegularOfDegree 3) {u v : V} (huv : H.Adj u v) :
    ∃ e : Fin 3 ≃ H.neighborSet u, (e 0).val = v := by
  classical
  let e : Fin 3 ≃ H.neighborSet u :=
    (Fintype.equivFinOfCardEq ((H.card_neighborSet_eq_degree u).trans (regular.degree_eq u))).symm
  let w : H.neighborSet u := ⟨v, huv⟩
  exact ⟨e.trans (Equiv.swap (e 0) w), by simp [w]⟩

/-- The two neighbor enumerations of an adjacent pair, with their shared edge first. -/
structure CubicPair (u v : V) where
  leftNeighbors : Fin 3 ≃ H.neighborSet u
  rightNeighbors : Fin 3 ≃ H.neighborSet v
  left_zero : (leftNeighbors 0).val = v
  right_zero : (rightNeighbors 0).val = u

theorem exists_cubicPair (regular : H.IsRegularOfDegree 3) {u v : V} (huv : H.Adj u v) :
    Nonempty (CubicPair H u v) := by
  obtain ⟨l, hl⟩ := exists_neighborEnum H regular huv
  obtain ⟨r, hr⟩ := exists_neighborEnum H regular huv.symm
  exact ⟨⟨l, r, hl, hr⟩⟩

namespace CubicPair

variable {H} {u v : V} (p : CubicPair H u v)

/-- The two centers followed by their four outer neighbors. -/
def vertices : Fin 6 → V :=
  ![u, v, (p.leftNeighbors 1).val, (p.leftNeighbors 2).val,
    (p.rightNeighbors 1).val, (p.rightNeighbors 2).val]

/-- The four outer edges in the order used by the Gaussian pair calculation. -/
def outerEdges (i : Fin 4) : Sym2 V :=
  s(p.vertices (![0, 0, 1, 1] i), p.vertices (![2, 3, 4, 5] i))

omit [Fintype V] [DecidableRel H.Adj] in
include p in
theorem adjacent : H.Adj u v := p.left_zero ▸ (p.leftNeighbors 0).property

omit [Fintype V] [DecidableRel H.Adj] in
theorem adjacent_endpoints (e : Fin 5) :
    H.Adj (p.vertices (criticalStarEndpoints e).1) (p.vertices (criticalStarEndpoints e).2) := by
  fin_cases e
  · exact p.adjacent
  · exact (p.leftNeighbors 1).property
  · exact (p.leftNeighbors 2).property
  · exact (p.rightNeighbors 1).property
  · exact (p.rightNeighbors 2).property

omit [Fintype V] [DecidableRel H.Adj] in
theorem adjacent_neighbors (b : Fin 2) (j : Fin 3) :
    H.Adj (p.vertices (criticalStarNeighbors b j)) (p.vertices (criticalStarCenter b)) := by
  fin_cases b <;> fin_cases j
  · exact p.adjacent.symm
  · exact (p.leftNeighbors 1).property.symm
  · exact (p.leftNeighbors 2).property.symm
  · exact p.adjacent
  · exact (p.rightNeighbors 1).property.symm
  · exact (p.rightNeighbors 2).property.symm

theorem outerEdges_mem (i : Fin 4) : p.outerEdges i ∈ H.edgeFinset := by
  apply SimpleGraph.mem_edgeFinset.mpr
  fin_cases i
  · exact (p.leftNeighbors 1).property
  · exact (p.leftNeighbors 2).property
  · exact (p.rightNeighbors 1).property
  · exact (p.rightNeighbors 2).property

/-- Enumerate all incident edges using a neighbor enumeration. -/
noncomputable def incidenceEnum {w : V} (e : Fin 3 ≃ H.neighborSet w) :
    Fin 3 ≃ ↥(H.incidenceFinset w) := by
  classical
  exact (e.trans (H.incidenceSetEquivNeighborSet w).symm).trans
    (Equiv.subtypeEquivRight fun _ => SimpleGraph.mem_incidenceFinset.symm)

theorem incidenceEnum_apply {w : V} (e : Fin 3 ≃ H.neighborSet w) (i : Fin 3) :
    (incidenceEnum e i).val = s(w, (e i).val) := rfl

theorem starGap_left (q ρ κ : ℝ) (R : ℕ) (hκ : κ ^ 2 = (1 + ρ) / 2) :
    starGap κ (fun j => edgeVector H q R
      s(p.vertices (criticalStarNeighbors 0 j), p.vertices (criticalStarCenter 0))) =
        edgeStarGap H q R ρ u := by
  rw [edgeStarGap_eq_starGap H q R ρ κ u (incidenceEnum p.leftNeighbors) hκ]
  congr 1
  funext j
  rw [incidenceEnum_apply]
  fin_cases j <;> simp [vertices, criticalStarNeighbors, criticalStarCenter,
    p.left_zero, Sym2.eq_swap]

theorem starGap_right (q ρ κ : ℝ) (R : ℕ) (hκ : κ ^ 2 = (1 + ρ) / 2) :
    starGap κ (fun j => edgeVector H q R
      s(p.vertices (criticalStarNeighbors 1 j), p.vertices (criticalStarCenter 1))) =
        edgeStarGap H q R ρ v := by
  rw [edgeStarGap_eq_starGap H q R ρ κ v (incidenceEnum p.rightNeighbors) hκ]
  congr 1
  funext j
  rw [incidenceEnum_apply]
  fin_cases j <;> simp [vertices, criticalStarNeighbors, criticalStarCenter,
    p.right_zero, Sym2.eq_swap]

end CubicPair

open MeasureTheory in
/-- Choose the gap tolerance before the desired singleton accuracy, and then
choose common Gaussian parameters before the graph. Every adjacent pair
whose two intrinsic star gaps are small then satisfies the local pair-cost
estimate, without supplying separate covariance or incidence certificates. -/
theorem exists_pair_estimate_parameters {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ {ξ : ℝ}, 0 < ξ → ∃ (q : ℝ) (R : ℕ) (ρ : ℝ),
      0 ≤ q ∧ 17 / 32 ≤ ρ ∧
      ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ∧
      straddleBound ρ ≤ gaussianCoefficient + ξ ∧
      ∀ {W : Type} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
        H.IsRegularOfDegree 3 → ∀ {u v : W} (p : CubicPair H u v),
          edgeStarGap H q R ρ u ≤ τ → edgeStarGap H q R ρ v ≤ τ →
          ∀ t, (∫ ω, twoVertexThresholdCost t
            (fun i => edgeScore H q R ω (p.outerEdges i)) ∂gaussPi W) ≤
              twoVertexTreeBound + ε := by
  obtain ⟨τ, hτ, hlocal⟩ := exists_unitKernel_pair_gap_tolerance hε
  refine ⟨τ, hτ, fun {ξ} hξ => ?_⟩
  obtain ⟨q, R, ρ, hq, hq₁, hρ, hρhi, hbound, htail, htail', hqnear, hρnear, hmean⟩ :=
    exists_pair_kernel_parameters hτ hξ
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hρ0 : -1 < ρ := by linarith only [hρ]
  let κ := Real.sqrt ((1 + ρ) / 2)
  have hκsq : κ ^ 2 = (1 + ρ) / 2 := Real.sq_sqrt (by linarith only [hρ])
  have hκbase : 2 * κ ^ 2 - 1 = ρ := by rw [hκsq]; ring
  have hκlo : 1 / 2 ≤ κ := (Real.le_sqrt (by norm_num) (by linarith only [hρ])).mpr
    (by norm_num; linarith only [hρ])
  have hκhi : κ ≤ 1 := (Real.sqrt_le_one).mpr (by
    have hs : Real.sqrt 2 < 3 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    linarith only [hρhi, hs])
  have hbase : 2 * κ ^ 2 - 1 ≤ 2 * q / (1 + q ^ 2) := by
    rw [hκbase]
    have ht : 0 ≤ 3 * (2 * q ^ 2) ^ R := by positivity
    linarith only [hbound, ht]
  refine ⟨q, R, ρ, hq0, hρ, hbound, hmean,
    fun {W} _ H _ regular {u v} p hu hv t => ?_⟩
  have degree : ∀ w, H.degree w ≤ 3 := fun w => (regular.degree_eq w).le
  apply hlocal H degree p.vertices p.adjacent_endpoints q κ hq hq₁ hκlo hκhi
    hbase R htail htail' hqnear (by simpa only [hκbase] using hρnear)
  · intro b j
    have hc := hbound.trans
      (sum_unitKernel_mul_ge H degree hq0 R (p.adjacent_neighbors b j))
    rw [pairNormSq_eq]
    linarith only [hc, hρ0]
  · intro b j
    apply (edgeVector_star degree hq0 hρ0 hbound _ ?_).2
    rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_iff]
    exact ⟨p.adjacent_neighbors b j, Or.inr rfl⟩
  · intro b
    fin_cases b
    · exact (p.starGap_left q ρ κ R hκsq).le.trans hu
    · exact (p.starGap_right q ρ κ R hκsq).le.trans hv

open MeasureTheory in
/-- The explicit star-gap tolerance gives a pair saving of `1/2000`,
with common finite kernel parameters and arbitrary singleton accuracy. -/
theorem exists_pair_estimate_parameters_explicit {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ (q : ℝ) (R : ℕ) (ρ : ℝ), 0 ≤ q ∧ 17 / 32 ≤ ρ ∧
      ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ∧
      straddleBound ρ ≤ gaussianCoefficient + ξ ∧
      ∀ {W : Type} [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
        H.IsRegularOfDegree 3 → ∀ {u v : W} (p : CubicPair H u v),
          edgeStarGap H q R ρ u ≤ pairGapTolerance →
          edgeStarGap H q R ρ v ≤ pairGapTolerance →
          ∀ t, (∫ ω, twoVertexThresholdCost t
            (fun i => edgeScore H q R ω (p.outerEdges i)) ∂gaussPi W) ≤
              2 * gaussianCoefficient - 1 / 2000 := by
  obtain ⟨q, R, ρ, hq, hq₁, hρ, hρhi, hbound, htail, htail', hqnear, hρnear, hmean⟩ :=
    exists_pair_kernel_parameters pairGapTolerance_pos hξ
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hρ0 : -1 < ρ := by linarith only [hρ]
  let κ := Real.sqrt ((1 + ρ) / 2)
  have hκsq : κ ^ 2 = (1 + ρ) / 2 := Real.sq_sqrt (by linarith only [hρ])
  have hκbase : 2 * κ ^ 2 - 1 = ρ := by rw [hκsq]; ring
  have hκlo : 1 / 2 ≤ κ := (Real.le_sqrt (by norm_num) (by linarith only [hρ])).mpr
    (by norm_num; linarith only [hρ])
  have hκhi : κ ≤ 1 := (Real.sqrt_le_one).mpr (by
    have hs : Real.sqrt 2 < 3 / 2 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    linarith only [hρhi, hs])
  have hbase : 2 * κ ^ 2 - 1 ≤ 2 * q / (1 + q ^ 2) := by
    rw [hκbase]
    have ht : 0 ≤ 3 * (2 * q ^ 2) ^ R := by positivity
    linarith only [hbound, ht]
  refine ⟨q, R, ρ, hq0, hρ, hbound, hmean,
    fun {W} _ H _ regular {u v} p hu hv t => ?_⟩
  have degree : ∀ w, H.degree w ≤ 3 := fun w => (regular.degree_eq w).le
  apply le_trans (b := twoVertexTreeBound + 1 / 5000)
  · apply unitKernel_pair_gap_explicit H degree p.vertices p.adjacent_endpoints
      q κ hq hq₁ hκlo hκhi hbase R htail htail' hqnear
      (by simpa only [hκbase] using hρnear)
    · intro b j
      have hc := hbound.trans
        (sum_unitKernel_mul_ge H degree hq0 R (p.adjacent_neighbors b j))
      rw [pairNormSq_eq]
      linarith only [hc, hρ0]
    · intro b j
      apply (edgeVector_star degree hq0 hρ0 hbound _ ?_).2
      rw [SimpleGraph.mem_incidenceFinset, SimpleGraph.mk'_mem_incidenceSet_iff]
      exact ⟨p.adjacent_neighbors b j, Or.inr rfl⟩
    · intro b
      fin_cases b
      · exact (p.starGap_left q ρ κ R hκsq).le.trans hu
      · exact (p.starGap_right q ρ κ R hκsq).le.trans hv
  · linarith [twoVertexTreeBound_le, two_mul_gaussianCoefficient_ge]

end Frontier.PairLayout

