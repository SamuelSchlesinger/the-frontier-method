/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.MatchingLayout

/-!
# Expected cost of disjoint Gaussian pairs

The exact matching partition lets singleton straddling probabilities and
optimized pair expectations be added without overlap. The local pair saving
therefore gives a linear saving in the expected cost at every fixed threshold
whenever a linear-size matching has small intrinsic star gaps. Controlling all
thresholds in one sample remains a separate concentration step.
-/

@[expose] public section

namespace Frontier.PairLayout

open Finset Gaussian MeasureTheory

variable {V : Type} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]

omit [DecidableEq V] in
/-- The three-port optimum is the indicator of a straddling star. -/
theorem starCost_eq_straddle {v : V} (E : Fin 3 ≃ H.neighborSet v)
    (score : Sym2 V → ℝ) (t : ℝ) :
    starCost (belowThreshold t (score s(v, (E 0).val)))
      (belowThreshold t (score s(v, (E 1).val)))
      (belowThreshold t (score s(v, (E 2).val))) =
        if EdgeStraddles H score t v then 1 else 0 := by
  let F := CubicPair.incidenceEnum E
  have hs : EdgeStraddles H score t v ↔
      (∃ i : Fin 3, score (F i) < t) ∧ (∃ i : Fin 3, t ≤ score (F i)) := by
    constructor
    · rintro ⟨e, he, hlow, f, hf, hhigh⟩
      obtain ⟨i, hi⟩ := F.surjective ⟨e, he⟩
      obtain ⟨j, hj⟩ := F.surjective ⟨f, hf⟩
      exact ⟨⟨i, hi ▸ hlow⟩, ⟨j, hj ▸ hhigh⟩⟩
    · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      exact ⟨F i, (F i).property, hi, F j, (F j).property, hj⟩
  simp only [Fin.exists_fin_succ] at hs
  by_cases h0 : score s(v, (E 0).val) < t <;>
    by_cases h1 : score s(v, (E 1).val) < t <;>
    by_cases h2 : score s(v, (E 2).val) < t <;>
    simp [starCost, belowThreshold, hs, F, CubicPair.incidenceEnum_apply, h0, h1, h2,
      not_lt.mp]

/-- Separate the expectation into singleton probabilities and pair expectations. -/
theorem integral_matchingCost (M : Finset (Sym2 V))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2) (q : ℝ) (R : ℕ) (t : ℝ) :
    (∫ ω, (matchingCost H M stars pairs
      (fun e => belowThreshold t (edgeScore H q R ω e)) : ℝ) ∂gaussPi V) =
      (∑ v ∈ singleVertices M, (gaussPi V).real (straddleEvent H q R t v)) +
      ∑ e : ↥M, ∫ ω, twoVertexThresholdCost t
        (fun i => edgeScore H q R ω ((pairs e).outerEdges i)) ∂gaussPi V := by
  have hs (v : V) :
      (fun ω => (starCost (belowThreshold t (edgeScore H q R ω s(v, (stars v 0).val)))
        (belowThreshold t (edgeScore H q R ω s(v, (stars v 1).val)))
        (belowThreshold t (edgeScore H q R ω s(v, (stars v 2).val))) : ℝ)) =
      (straddleEvent H q R t v).indicator 1 := by
    funext ω
    rw [starCost_eq_straddle]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Set.indicator_apply,
      straddleEvent, Set.mem_ofPred_eq, Pi.one_apply]
  have hi (v : V) : Integrable ((straddleEvent H q R t v).indicator
      (1 : (V → ℝ) → ℝ)) (gaussPi V) :=
    (integrable_const 1).indicator (measurableSet_straddleEvent q R t v)
  have hp (e : ↥M) : Integrable (fun ω => twoVertexThresholdCost t
      (fun i => edgeScore H q R ω ((pairs e).outerEdges i))) (gaussPi V) :=
    integrable_twoVertexThresholdCost _ _
      (Measurable.of_eval fun i => measurable_edgeScore H q R _) t
  simp only [matchingCost, Nat.cast_add, Nat.cast_sum]
  simp_rw [show ∀ v ω,
    (starCost (belowThreshold t (edgeScore H q R ω s(v, (stars v 0).val)))
      (belowThreshold t (edgeScore H q R ω s(v, (stars v 1).val)))
      (belowThreshold t (edgeScore H q R ω s(v, (stars v 2).val))) : ℝ) =
    (straddleEvent H q R t v).indicator 1 ω from fun v ω => congrFun (hs v) ω]
  change (∫ ω, (∑ v ∈ singleVertices M, (straddleEvent H q R t v).indicator 1 ω) +
    ∑ e : ↥M, twoVertexThresholdCost t
      (fun i => edgeScore H q R ω ((pairs e).outerEdges i)) ∂gaussPi V) = _
  rw [integral_add (integrable_finsetSum _ fun v _ => hi v)
    (integrable_finsetSum _ fun e _ => hp e),
    integral_finsetSum _ fun v _ => hi v, integral_finsetSum _ fun e _ => hp e]
  congr 1
  exact sum_congr rfl fun v _ => integral_indicator_one (measurableSet_straddleEvent q R t v)

/-- Any uniform pair estimate adds to the existing singleton estimate. -/
theorem integral_matchingCost_le (regular : H.IsRegularOfDegree 3)
    (M : Finset (Sym2 V))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2)
    {q ρ B : ℝ} {R : ℕ} (hq : 0 ≤ q) (hρ : 17 / 32 ≤ ρ)
    (hbound : ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    (hpair : ∀ e : ↥M, ∀ t, (∫ ω, twoVertexThresholdCost t
      (fun i => edgeScore H q R ω ((pairs e).outerEdges i)) ∂gaussPi V) ≤ B) (t : ℝ) :
    (∫ ω, (matchingCost H M stars pairs
      (fun e => belowThreshold t (edgeScore H q R ω e)) : ℝ) ∂gaussPi V) ≤
        (singleVertices M).card * straddleBound ρ + M.card * B := by
  rw [integral_matchingCost]
  calc
    _ ≤ (∑ _v ∈ singleVertices M, straddleBound ρ) + ∑ _e : ↥M, B :=
      add_le_add (sum_le_sum fun v _ => measureReal_straddleEvent_le regular hq hρ hbound t v)
        (sum_le_sum fun e _ => hpair e t)
    _ = _ := by simp

/-- A matching covering at least two fifths of the vertices turns a pair saving
into a saving in the total mean, allowing a small singleton error. -/
theorem integral_matchingCost_le_of_saving (regular : H.IsRegularOfDegree 3)
    (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2)
    {q ρ p ε η : ℝ} {R : ℕ} (hq : 0 ≤ q) (hρ : 17 / 32 ≤ ρ)
    (hbound : ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    (hmean : straddleBound ρ ≤ p + η) (hη : 0 ≤ η) (hε : 10 * η ≤ ε)
    (hpair : ∀ e : ↥M, ∀ t, (∫ ω, twoVertexThresholdCost t
      (fun i => edgeScore H q R ω ((pairs e).outerEdges i)) ∂gaussPi V) ≤ 2 * p - ε)
    (hsize : Fintype.card V ≤ 5 * M.card) (t : ℝ) :
    (∫ ω, (matchingCost H M stars pairs
      (fun e => belowThreshold t (edgeScore H q R ω e)) : ℝ) ∂gaussPi V) ≤
        Fintype.card V * (p - η) := by
  have hb := integral_matchingCost_le H regular M stars pairs hq hρ hbound hpair t
  have hc : ((singleVertices M).card : ℝ) + 2 * M.card = Fintype.card V := by
    exact_mod_cast card_singleVertices_add_two_mul H M hM hdisj
  have hn : (Fintype.card V : ℝ) ≤ 5 * M.card := by exact_mod_cast hsize
  have hs := mul_le_mul_of_nonneg_left hmean (Nat.cast_nonneg (singleVertices M).card)
  have hnη := mul_le_mul_of_nonneg_right hn hη
  have hMε := mul_le_mul_of_nonneg_left hε (Nat.cast_nonneg M.card : (0 : ℝ) ≤ M.card)
  have hMη := mul_nonneg (Nat.cast_nonneg M.card : (0 : ℝ) ≤ M.card) hη
  have hcp := congrArg (fun x : ℝ => x * p) hc
  have hcη := congrArg (fun x : ℝ => x * η) hc
  nlinarith only [hb, hs, hnη, hMε, hMη, hcp, hcη]

/-- Either the singleton gaps already save `η`, or a large matching of small-gap
vertices converts the local pair saving into the same global mean saving. -/
theorem exists_matching_of_pair_estimate (regular : H.IsRegularOfDegree 3)
    {q ρ p ε η τ : ℝ} {R : ℕ} (hq : 0 ≤ q) (hρ : 17 / 32 ≤ ρ)
    (hbound : ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    (hmean : straddleBound ρ ≤ p + η) (hη : 0 < η) (hηε : 10 * η ≤ ε)
    (hτ : 0 < τ) (hητ : 2 * η ≤ τ / (24 * Real.pi))
    (hpair : ∀ {u v : V} (pair : CubicPair H u v),
      edgeStarGap H q R ρ u ≤ τ → edgeStarGap H q R ρ v ≤ τ →
      ∀ t, (∫ ω, twoVertexThresholdCost t
        (fun i => edgeScore H q R ω (pair.outerEdges i)) ∂gaussPi V) ≤ 2 * p - ε) :
    ∃ (M : Finset (Sym2 V)) (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
      (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2),
      M ⊆ H.edgeFinset ∧
      (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset) ∧
      ∀ t, (∫ ω, (matchingCost H M stars pairs
        (fun e => belowThreshold t (edgeScore H q R ω e)) : ℝ) ∂gaussPi V) ≤
          Fintype.card V * (p - η) := by
  classical
  let stars (v : V) : Fin 3 ≃ H.neighborSet v :=
    (Fintype.equivFinOfCardEq ((H.card_neighborSet_eq_degree v).trans (regular.degree_eq v))).symm
  by_cases hbig : (Fintype.card V : ℝ) * (τ / 6) ≤ ∑ v, edgeStarGap H q R ρ v
  · let pairs (e : ↥(∅ : Finset (Sym2 V))) : CubicPair H e.val.out.1 e.val.out.2 :=
      isEmptyElim e
    refine ⟨∅, stars, pairs, empty_subset _, by simp, fun t => ?_⟩
    rw [integral_matchingCost]
    suffices hm : (∑ v, (gaussPi V).real (straddleEvent H q R t v)) ≤
        Fintype.card V * (p - η) by
      simpa [singleVertices, matchedVertices] using hm
    have hm := sum_measureReal_straddleEvent_add_gap_le regular hq hρ hbound t
    have hg := div_le_div_of_nonneg_right hbig (by positivity : 0 ≤ 4 * Real.pi)
    have he : (Fintype.card V : ℝ) * (τ / 6) / (4 * Real.pi) =
        Fintype.card V * (τ / (24 * Real.pi)) := by ring
    rw [he] at hg
    calc
      _ ≤ Fintype.card V * (straddleBound ρ - τ / (24 * Real.pi)) := by
        nlinarith only [hm, hg]
      _ ≤ Fintype.card V * (p - η) :=
        mul_le_mul_of_nonneg_left (by linarith only [hmean, hητ]) (Nat.cast_nonneg _)
  · obtain ⟨M, hM, hdisj, hgood, hcount⟩ := exists_matching_small_gap H regular
      (edgeStarGap H q R ρ) (edgeStarGap_nonneg regular hq (by linarith) hbound) hτ
    have hsize : Fintype.card V ≤ 5 * M.card := by
      have hsmall := (lt_of_not_ge hbig).le
      have hc : (Fintype.card V : ℝ) ≤ 5 * M.card := by
        by_contra! hn
        have hp := mul_pos hτ (sub_pos.mpr hn)
        nlinarith
      exact_mod_cast hc
    let pairs (e : ↥M) : CubicPair H e.val.out.1 e.val.out.2 :=
      Classical.choice (exists_cubicPair H regular (adjacent_out H (hM e.property)))
    refine ⟨M, stars, pairs, hM, hdisj, ?_⟩
    apply integral_matchingCost_le_of_saving H regular M hM hdisj stars pairs hq hρ hbound
      hmean hη.le hηε _ hsize
    intro e t
    exact hpair (pairs e)
      (hgood e.val e.property _ (Sym2.out_fst_mem e.val))
      (hgood e.val e.property _ (Sym2.out_snd_mem e.val)) t

/-- Common finite-radius Gaussian parameters give every cubic graph a matching
whose optimized cost has a strictly improved mean at every fixed threshold.
This does not yet choose one sample controlling all thresholds. -/
theorem exists_uniform_matching_mean_saving :
    ∃ (q : ℝ) (R : ℕ) (ρ η : ℝ), 0 ≤ q ∧ 17 / 32 ≤ ρ ∧
      ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ∧ 0 < η ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
        H.IsRegularOfDegree 3 →
        ∃ (M : Finset (Sym2 W)) (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
          (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2),
          M ⊆ H.edgeFinset ∧
          (M : Set (Sym2 W)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset) ∧
          ∀ t, (∫ ω, (matchingCost H M stars pairs
            (fun e => belowThreshold t (edgeScore H q R ω e)) : ℝ) ∂gaussPi W) ≤
              Fintype.card W * (gaussianCoefficient - η) := by
  classical
  let ε := (2 * gaussianCoefficient - twoVertexTreeBound) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith only [twoVertexTreeBound_lt_two_mul_gaussianCoefficient]
  obtain ⟨τ, hτ, hparams⟩ := exists_pair_estimate_parameters hε
  let η := min (ε / 10) (τ / (48 * Real.pi))
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηε : 10 * η ≤ ε := by
    have := min_le_left (ε / 10) (τ / (48 * Real.pi))
    dsimp [η]
    linarith
  have hητ : 2 * η ≤ τ / (24 * Real.pi) := by
    have := min_le_right (ε / 10) (τ / (48 * Real.pi))
    have he : τ / (24 * Real.pi) = 2 * (τ / (48 * Real.pi)) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left this (by norm_num)
  obtain ⟨q, R, ρ, hq, hρ, hbound, hmean, hpair⟩ := hparams hη
  refine ⟨q, R, ρ, η, hq, hρ, hbound, hη, fun {W} _ _ H _ regular => ?_⟩
  apply exists_matching_of_pair_estimate H regular hq hρ hbound hmean hη hηε hτ hητ
  intro u v pair hu hv t
  have hp := hpair H regular pair hu hv t
  have he : twoVertexTreeBound + ε = 2 * gaussianCoefficient - ε := by dsimp [ε]; ring
  rwa [he] at hp

/-- A conservative explicit saving in the uniform expected cost per cubic vertex. -/
noncomputable def matchingMeanSaving : ℝ := 1 / 10 ^ 48

theorem matchingMeanSaving_pos : 0 < matchingMeanSaving := by norm_num [matchingMeanSaving]

/-- Every cubic graph admits a matching with mean saving `10⁻⁴⁸`, using
common Gaussian parameters chosen independently of the graph. -/
theorem exists_uniform_matching_mean_explicit :
    ∃ (q : ℝ) (R : ℕ) (ρ : ℝ), 0 ≤ q ∧ 17 / 32 ≤ ρ ∧
      ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
        H.IsRegularOfDegree 3 →
        ∃ (M : Finset (Sym2 W)) (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
          (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2),
          M ⊆ H.edgeFinset ∧
          (M : Set (Sym2 W)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset) ∧
          ∀ t, (∫ ω, (matchingCost H M stars pairs
            (fun e => belowThreshold t (edgeScore H q R ω e)) : ℝ) ∂gaussPi W) ≤
              Fintype.card W * (gaussianCoefficient - matchingMeanSaving) := by
  obtain ⟨q, R, ρ, hq, hρ, hbound, hmean, hpair⟩ :=
    exists_pair_estimate_parameters_explicit matchingMeanSaving_pos
  refine ⟨q, R, ρ, hq, hρ, hbound, fun {W} _ _ H _ regular => ?_⟩
  apply exists_matching_of_pair_estimate H regular hq hρ hbound hmean
    matchingMeanSaving_pos (ε := 1 / 2000) (τ := pairGapTolerance)
    (by norm_num [matchingMeanSaving]) pairGapTolerance_pos ?_ (hpair H regular)
  rw [le_div_iff₀ (by positivity : 0 < 24 * Real.pi)]
  dsimp [matchingMeanSaving, pairGapTolerance]
  nlinarith [Real.pi_le_four]

end Frontier.PairLayout
