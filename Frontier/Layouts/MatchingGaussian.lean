/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Layouts.MatchingGrid

/-!
# Simultaneous Gaussian matching layouts

A union bound chooses one Gaussian sample controlling every grid cost,
edge-score window, and tail. The deterministic matching-grid theorem turns
these simultaneous bounds into one injective ordering, including tied keys.
-/

@[expose] public section

namespace Frontier.PairLayout

open Finset Gaussian MeasureTheory ProbabilityTheory

variable {V : Type} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]

private structure Concentrated (M : Finset (Sym2 V))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2)
    (q : ℝ) (R : ℕ) (T ε : ℝ) (N : ℕ) (ω : V → ℝ) : Prop where
  cost (i : ℕ) (hi : i < N) :
    |(matchingCost H M stars pairs
        (fun e => belowThreshold (-T + i * (2 * T / N)) (edgeScore H q R ω e)) : ℝ) -
      ∫ ω', (matchingCost H M stars pairs
        (fun e => belowThreshold (-T + i * (2 * T / N)) (edgeScore H q R ω' e)) : ℝ)
          ∂gaussPi V| < ε * Fintype.card V
  window (i : ℕ) (hi : i < N) :
    ω ∉ deviation H.edgeFinset
      (edgeScoreEvent H q R
        (fun x => -T + i * (2 * T / N) ≤ x ∧ x < -T + i * (2 * T / N) + 2 * T / N))
      (ε * Fintype.card V)
  low : ω ∉ deviation H.edgeFinset (edgeScoreEvent H q R (· < -T)) (ε * Fintype.card V)
  high : ω ∉ deviation H.edgeFinset (edgeScoreEvent H q R (T ≤ ·)) (ε * Fintype.card V)

private theorem exists_concentrated (regular : H.IsRegularOfDegree 3)
    (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2)
    (q : ℝ) (R : ℕ) (T : ℝ) {ε : ℝ} (hε : 0 < ε) (N : ℕ)
    (large : (6 * N + 3) * (vertexOverlap 3 (R + 2) : ℝ) / ε ^ 2 < Fintype.card V) :
    ∃ ω, Concentrated H M stars pairs q R T ε N ω := by
  classical
  have degree : ∀ v, H.degree v ≤ 3 := fun v => (regular.degree_eq v).le
  set h : ℝ := (Fintype.card V : ℝ)
  set P := gaussPi V
  set D : ℝ := (vertexOverlap 3 (R + 2) : ℝ)
  set δ : ℝ := 2 * T / N
  have hh : 0 < h := lt_of_le_of_lt (by positivity) large
  set c : ℝ := ε * h with hc
  have hcpos : 0 < c := mul_pos hε hh
  have hE := card_edgeFinset_of_regular regular
  let thr (i : ℕ) := -T + i * δ
  let costDev (i : ℕ) := {ω |
    c ≤ |(matchingCost H M stars pairs
        (fun e => belowThreshold (thr i) (edgeScore H q R ω e)) : ℝ) -
      ∫ ω', (matchingCost H M stars pairs
        (fun e => belowThreshold (thr i) (edgeScore H q R ω' e)) : ℝ) ∂gaussPi V|}
  let window (i : ℕ) := edgeScoreEvent H q R (fun x => thr i ≤ x ∧ x < thr i + δ)
  let low := edgeScoreEvent H q R (fun x => x < -T)
  let high := edgeScoreEvent H q R (fun x => T ≤ x)
  let bad := ((⋃ i ∈ range N, (costDev i ∪ deviation H.edgeFinset (window i) c)) ∪
    deviation H.edgeFinset low c) ∪ deviation H.edgeFinset high c
  have costDev_le (i) : P.real (costDev i) ≤ 4 * h * D / c ^ 2 :=
    measureReal_matchingCost_deviation_le H regular M hM hdisj stars pairs q R (thr i) hcpos
  have edgeDev : ∀ {p : ℝ → Prop}, MeasurableSet {x | p x} →
      P.real (deviation H.edgeFinset (edgeScoreEvent H q R p) c) ≤
        #H.edgeFinset * D / c ^ 2 := by
    intro p hp
    have hd : vertexOverlap 3 R ≤ vertexOverlap 3 (R + 2) := by
      unfold vertexOverlap
      exact Nat.pow_le_pow_right (by norm_num) (by lia)
    refine (pi_deviation_le (fun _ : V => gaussianReal 0 1) H.edgeFinset
      (edgeScoreEvent H q R p) (edgeSupport H R)
      (fun e _ => measurableSet_edgeScoreEvent q R hp e)
      (fun e _ => dependsOn_edgeScoreEvent q R p e)
      (fun e he => edge_overlap_le H (by norm_num) degree R he) hcpos).trans ?_
    gcongr
    dsimp only [D]
    exact_mod_cast hd
  have hbad : P.real bad < 1 := by
    have hu : P.real bad ≤ ∑ i ∈ range N,
        (4 * h * D / c ^ 2 + #H.edgeFinset * D / c ^ 2) +
          #H.edgeFinset * D / c ^ 2 + #H.edgeFinset * D / c ^ 2 := by
      refine (measureReal_union_le _ _).trans (add_le_add ?_
        (edgeDev (measurableSet_le measurable_const measurable_id)))
      refine (measureReal_union_le _ _).trans (add_le_add ?_
        (edgeDev (measurableSet_lt measurable_id measurable_const)))
      refine (measureReal_biUnion_finset_le _ _).trans (sum_le_sum fun i _ => ?_)
      exact (measureReal_union_le _ _).trans (add_le_add (costDev_le i)
        (edgeDev ((measurableSet_le measurable_const measurable_id).inter
          (measurableSet_lt measurable_id measurable_const))))
    rw [sum_const, card_range, nsmul_eq_mul, hE] at hu
    refine hu.trans_lt ?_
    have hD : 0 ≤ D := by positivity
    have he : (N * (4 * h * D / c ^ 2 + 3 / 2 * h * D / c ^ 2) +
        3 / 2 * h * D / c ^ 2 + 3 / 2 * h * D / c ^ 2) =
        (11 / 2 * N + 3) * D / ε ^ 2 / h := by
      rw [hc]
      field_simp
      ring
    rw [he, div_lt_one hh]
    calc
      (11 / 2 * (N : ℝ) + 3) * D / ε ^ 2 ≤ (6 * N + 3) * D / ε ^ 2 := by
        gcongr
        linarith
      _ < h := large
  obtain ⟨ω, hω⟩ : ∃ ω, ω ∉ bad := by
    by_contra! hall
    have hb : bad = Set.univ := Set.eq_univ_of_forall hall
    rw [hb, probReal_univ] at hbad
    exact lt_irrefl _ hbad
  simp only [bad, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hω
  obtain ⟨⟨hmid, hlo⟩, hhi⟩ := hω
  refine ⟨ω, fun i hi => ?_, fun i hi => (hmid i (mem_range.mpr hi)).2, hlo, hhi⟩
  simpa only [costDev, Set.mem_ofPred_eq, not_le] using (hmid i (mem_range.mpr hi)).1

/-- Mean, window, deviation, and tail contributions to the matching layout bound. -/
noncomputable def matchingBoundOfMean (μ T ε : ℝ) (N : ℕ) : ℝ :=
  max (81 / T ^ 2 + 54 * ε)
    (μ + 81 * (2 * T / N) / Real.sqrt (2 * Real.pi) + 55 * ε)

/-- A uniform bound on expected matching costs survives simultaneous concentration
and yields one ordering controlling every prefix. -/
theorem exists_matching_sample_of_mean (regular : H.IsRegularOfDegree 3)
    (M : Finset (Sym2 V)) (hM : M ⊆ H.edgeFinset)
    (hdisj : (M : Set (Sym2 V)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset))
    (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
    (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2)
    {q ρ : ℝ} (hq : 0 ≤ q) (R : ℕ) (hρ : 17 / 32 ≤ ρ)
    (hbound : ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) {N : ℕ} (hN : 0 < N)
    (large : (6 * N + 3) * (vertexOverlap 3 (R + 2) : ℝ) / ε ^ 2 < Fintype.card V)
    {μ : ℝ} (hmean : ∀ t, (∫ ω, (matchingCost H M stars pairs
      (fun e => belowThreshold t (edgeScore H q R ω e)) : ℝ) ∂gaussPi V) ≤
        Fintype.card V * μ) :
    ∃ key : V → ℕ, Function.Injective key ∧ ∀ t,
      ((H.cutFinset {v | key v < t}).card : ℝ) ≤
        Fintype.card V * matchingBoundOfMean μ T ε N := by
  classical
  have degree : ∀ v, H.degree v ≤ 3 := fun v => (regular.degree_eq v).le
  set h : ℝ := (Fintype.card V : ℝ)
  set P := gaussPi V
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set δ : ℝ := 2 * T / N with hδ
  have hδpos : 0 < δ := by positivity
  have hhpos : 0 < h := lt_of_le_of_lt (by positivity) large
  set c : ℝ := ε * h with hc
  have hE := card_edgeFinset_of_regular regular
  have hρ' : -1 < ρ := by linarith
  have unit := fun {e : Sym2 V} (he : e ∈ H.edgeFinset) =>
    sum_edgeVector_sq_of_mem degree hq hρ' hbound he
  obtain ⟨ω, good⟩ := exists_concentrated H regular M hM hdisj stars pairs q R T hε N large
  let thr (i : ℕ) := -T + i * δ
  let window (i : ℕ) := edgeScoreEvent H q R (fun x => thr i ≤ x ∧ x < thr i + δ)
  let low := edgeScoreEvent H q R (fun x => x < -T)
  let high := edgeScoreEvent H q R (fun x => T ≤ x)
  set X := edgeScore H q R ω
  have edgeMean : ∀ {p : ℝ → Prop} {b : ℝ}, (∀ e ∈ H.edgeFinset,
      P.real (edgeScoreEvent H q R p e) ≤ b) →
      ∑ e ∈ H.edgeFinset, P.real (edgeScoreEvent H q R p e) ≤ #H.edgeFinset * b :=
    fun hb => (sum_le_sum hb).trans_eq (by rw [sum_const, nsmul_eq_mul])
  have tailMean : ∀ e ∈ H.edgeFinset,
      P.real (low e) ≤ 1 / T ^ 2 ∧ P.real (high e) ≤ 1 / T ^ 2 :=
    fun e he => ⟨(measureReal_mono fun ω' hω' => by
      simp only [low, edgeScoreEvent, edgeScore, Set.mem_ofPred_eq] at hω' ⊢
      rw [abs_of_neg (by linarith)]; linarith).trans (gaussPi_tail_le _ (unit he) hT),
      (measureReal_mono fun ω' hω' => by
      simp only [high, edgeScoreEvent, edgeScore, Set.mem_ofPred_eq] at hω' ⊢
      exact hω'.trans (le_abs_self _)).trans (gaussPi_tail_le _ (unit he) hT)⟩
  have tail : ∀ (p : ℝ → Prop) [DecidablePred p],
      (∀ e ∈ H.edgeFinset, P.real (edgeScoreEvent H q R p e) ≤ 1 / T ^ 2) →
      ω ∉ deviation H.edgeFinset (edgeScoreEvent H q R p) c →
      54 * (#{e ∈ H.edgeFinset | p (X e)} : ℝ) ≤ h * (81 / T ^ 2 + 54 * ε) := by
    intro p _ hm hdev
    have hlt := lt_of_notMem_deviation hdev
    have hcount := card_filter_le_sum_indicator H.edgeFinset (edgeScoreEvent H q R p) ω
      (fun e => p (X e)) fun e _ hpe => hpe
    have := edgeMean hm
    calc
      54 * (#{e ∈ H.edgeFinset | p (X e)} : ℝ) ≤
          54 * (#H.edgeFinset * (1 / T ^ 2) + c) := by linarith
      _ = h * (81 / T ^ 2 + 54 * ε) := by rw [hE, hc]; field_simp; ring
  have hB1 : h * (81 / T ^ 2 + 54 * ε) ≤ h * matchingBoundOfMean μ T ε N :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hhpos.le
  have hB2 : h * (μ + 81 * δ / Real.sqrt (2 * Real.pi) + 55 * ε) ≤
      h * matchingBoundOfMean μ T ε N :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hhpos.le
  apply exists_key_of_matching_grid H regular M hM hdisj stars pairs X hδpos N
    (a := -T) (B := h * matchingBoundOfMean μ T ε N)
  · exact (tail (· < -T) (fun e he => (tailMean e he).1) good.low).trans hB1
  · have hT' : -T + N * δ = T := by rw [hδ]; field_simp; ring
    rw [hT']
    exact (tail (T ≤ ·) (fun e he => (tailMean e he).2) good.high).trans hB1
  · intro i hi
    have hC := (abs_lt.mp (good.cost i hi)).2
    have hW := lt_of_notMem_deviation (good.window i hi)
    have hWcount := card_filter_le_sum_indicator H.edgeFinset (window i) ω
      (fun e => -T + i * δ ≤ X e ∧ X e < -T + (i + 1) * δ) fun e _ he =>
        ⟨he.1, by simp only [thr]; linarith [he.2]⟩
    have hCmean := hmean (thr i)
    have hWmean := edgeMean (p := fun x => thr i ≤ x ∧ x < thr i + δ)
      (b := δ / Real.sqrt (2 * Real.pi)) fun e he =>
      gaussPi_window_le _ (unit he) (thr i) hδpos.le
    calc
      (matchingCost H M stars pairs (fun e => belowThreshold (-T + i * δ) (X e)) : ℝ) +
          54 * #{e ∈ H.edgeFinset | -T + i * δ ≤ X e ∧ X e < -T + (i + 1) * δ}
        ≤ (h * μ + c) + 54 * (#H.edgeFinset * (δ / Real.sqrt (2 * Real.pi)) + c) := by
          gcongr
          · linarith
          · linarith
      _ = h * (μ + 81 * δ / Real.sqrt (2 * Real.pi) + 55 * ε) := by rw [hE, hc]; ring
      _ ≤ _ := hB2

/-- The finite grid and deviations can consume less than half a fixed positive saving. -/
theorem exists_matching_parameters {η : ℝ} (hη : 0 < η) (hηle : η ≤ 1 / 100) :
    ∃ (ε : ℝ) (N : ℕ), 0 < ε ∧ 0 < N ∧
      matchingBoundOfMean (gaussianCoefficient - η) 100 ε N ≤ gaussianCoefficient - η / 2 := by
  let ε := η / 220
  let N : ℕ := ⌈32400 / η⌉₊ + 1
  have hN : 0 < N := Nat.succ_pos _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNR : 32400 / η ≤ N := by dsimp [N]; push_cast; linarith [Nat.le_ceil (32400 / η)]
  have hsqrtpi : 2 ≤ Real.sqrt (2 * Real.pi) :=
    (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [Real.two_le_pi])
  have hgrid : 81 * (2 * 100 / N) / Real.sqrt (2 * Real.pi) ≤ η / 4 := by
    rw [div_le_iff₀ (by positivity)]
    calc
      81 * (2 * 100 / (N : ℝ)) = 16200 / N := by ring
      _ ≤ η / 2 := by
        rw [div_le_iff₀ hNpos]
        have hm := mul_le_mul_of_nonneg_left hNR hη.le
        rw [mul_div_cancel₀ _ hη.ne'] at hm
        linarith
      _ ≤ η / 4 * Real.sqrt (2 * Real.pi) := by nlinarith
  refine ⟨ε, N, by positivity, hN, max_le ?_ ?_⟩
  · dsimp [ε]
    norm_num
    linarith [gaussianCoefficient_ge]
  · dsimp [ε]
    linarith

/-- Simultaneous concentration consumes at most half of any uniform mean saving. -/
theorem cubicLayoutBound_of_uniform_matching_mean {η : ℝ} (hη : 0 < η)
    (hηle : η ≤ 1 / 100)
    (hparams : ∃ (q : ℝ) (R : ℕ) (ρ : ℝ), 0 ≤ q ∧ 17 / 32 ≤ ρ ∧
      ρ ≤ 2 * q / (1 + q ^ 2) - 3 * (2 * q ^ 2) ^ R ∧
      ∀ {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
        H.IsRegularOfDegree 3 →
        ∃ (M : Finset (Sym2 W)) (stars : ∀ v, Fin 3 ≃ H.neighborSet v)
          (pairs : ∀ e : ↥M, CubicPair H e.val.out.1 e.val.out.2),
          M ⊆ H.edgeFinset ∧
          (M : Set (Sym2 W)).Pairwise (fun e f => Disjoint e.toFinset f.toFinset) ∧
          ∀ t, (∫ ω, (matchingCost H M stars pairs
            (fun e => belowThreshold t (edgeScore H q R ω e)) : ℝ) ∂gaussPi W) ≤
              Fintype.card W * (gaussianCoefficient - η)) :
    CubicLayoutBound (gaussianCoefficient - η / 2) := by
  classical
  obtain ⟨q, R, ρ, hq, hρ, hbound, hmean⟩ := hparams
  obtain ⟨ε, N, hε, hN, hgrid⟩ := exists_matching_parameters hη hηle
  intro ξ hξ
  refine ⟨⌈(6 * N + 3) * (vertexOverlap 3 (R + 2) : ℝ) / ε ^ 2⌉₊,
    fun W _ _ H _ regular large => ?_⟩
  have hlarge : (6 * N + 3) * (vertexOverlap 3 (R + 2) : ℝ) / ε ^ 2 < Fintype.card W :=
    (Nat.le_ceil _).trans_lt (by exact_mod_cast large)
  obtain ⟨M, stars, pairs, hM, hdisj, hm⟩ := hmean H regular
  obtain ⟨key, hinj, hkey⟩ := exists_matching_sample_of_mean H regular M hM hdisj stars pairs
    hq R hρ hbound (by norm_num : (0 : ℝ) < 100) hε hN hlarge hm
  refine ⟨key, hinj, fun t => ?_⟩
  have hp := mul_le_mul_of_nonneg_left hgrid (Nat.cast_nonneg (Fintype.card W) :
    (0 : ℝ) ≤ Fintype.card W)
  have hx := mul_nonneg hξ.le (Nat.cast_nonneg (Fintype.card W) : (0 : ℝ) ≤ Fintype.card W)
  nlinarith [hkey t]

/-- Disjoint pair optimization strictly improves the universal cubic layout coefficient. -/
theorem exists_cubicLayoutBound_lt_gaussian :
    ∃ p : ℝ, 0 < p ∧ p < gaussianCoefficient ∧ CubicLayoutBound p := by
  obtain ⟨q, R, ρ, η₀, hq, hρ, hbound, hη₀, hmean⟩ := exists_uniform_matching_mean_saving
  let η := min η₀ (1 / 100)
  have hη : 0 < η := lt_min hη₀ (by norm_num)
  have hηle : η ≤ 1 / 100 := min_le_right _ _
  have hη₀le : η ≤ η₀ := min_le_left _ _
  refine ⟨gaussianCoefficient - η / 2, by linarith [gaussianCoefficient_ge],
    by linarith, cubicLayoutBound_of_uniform_matching_mean hη hηle ?_⟩
  refine ⟨q, R, ρ, hq, hρ, hbound, fun {W} _ _ H _ regular => ?_⟩
  obtain ⟨M, stars, pairs, hM, hdisj, hm⟩ := hmean H regular
  exact ⟨M, stars, pairs, hM, hdisj, fun t =>
    (hm t).trans (mul_le_mul_of_nonneg_left (by linarith only [hη₀le]) (Nat.cast_nonneg _))⟩

/-- An explicit improvement of `10⁻⁴⁸ / 2` in the universal cubic layout coefficient. -/
theorem cubicLayoutBound_matching_explicit :
    CubicLayoutBound (gaussianCoefficient - matchingMeanSaving / 2) :=
  cubicLayoutBound_of_uniform_matching_mean matchingMeanSaving_pos
    (by norm_num [matchingMeanSaving]) exists_uniform_matching_mean_explicit

end Frontier.PairLayout
