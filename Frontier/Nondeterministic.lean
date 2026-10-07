/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Projection
public import Frontier.LowerBound
public import Frontier.Layouts

/-!
# Nondeterministic circuit lower bounds

A verifier has `n` ordinary inputs and `k` existential witness inputs, with no restriction on
`k`. Hiding the witnesses preserves the compiler graph and its degree and size bounds. The
cycle count subtracts every reachable ordinary input and every reachable witness input.
The same dense rectangle-free families therefore have the same lower bound, uniformly in
the number of witness inputs. Keeping the witness term and the logarithmic compression
overhead gives the stronger bound `s > (L - ε)n + |readWitnesses c|` for `s ≤ n^D`, with
fixed `D`. Repeated reads count once; unused declared witnesses do not count.
-/

@[expose] public section

namespace Frontier

open Cslib.Circuits Set Filter Asymptotics

universe u v

variable {U : Type u} {σ : Signature.{v}} {n k : ℕ}

/-- A verifier accepts an ordinary input exactly when some witness makes its output accepting. -/
def NondeterministicDecides (c : Circuit σ (n + k) 1) (I : Interpretation σ U) (Acc : Set U)
    (S : Set (Fin n → U)) : Prop :=
  ∀ x, x ∈ S ↔ ∃ y : Fin k → U, c.eval I (Fin.append x y) 0 ∈ Acc

/-- The distinct witness inputs reachable from the verifier's output. This is a property of
the wiring: unused declared witnesses do not count, and repeated reads count only once. -/
def readWitnesses (c : Circuit σ (n + k) 1) : Set (Fin k) :=
  {j | Compiler.Reach c.program c.outputs (.input (Fin.natAdd n j))}

variable [Finite U] [Nontrivial U]

/-- Hiding witnesses preserves the compiler graph. Its cycle rank still receives credit for
every distinct reachable witness input, as well as the ordinary inputs. -/
theorem exists_graph_of_nondeterministic_decides_witnesses {I : Interpretation σ U} {Acc : Set U}
    {c : Circuit σ (n + k) 1} {S : Set (Fin n → U)} {K r : ℕ}
    (hr : 2 ≤ r) (hfan : c.FanInAtMost r) (hS : NondeterministicDecides c I Acc S)
    (hfree : RectangleFree S K) (hbig : Nat.card U * K ^ 2 ≤ S.ncard) :
    ∃ (V E : Type) (_ : Finite V) (_ : Finite E) (G : Multigraph V E),
      G.Connected ∧ G.Loopless ∧ G.MaxDegreeLE (r + 1) ∧
      Nat.card V ≤ 2 * r * c.innerSize + 3 ∧
      (G.cycleRank : ℝ) ≤ ((r - 1) * c.innerSize : ℕ) - (readWitnesses c).ncard - n +
        Real.logb (Nat.card U) K + 1 ∧
      ∀ (π : Layout V) (w : ℕ), (∀ t, (G.cut (π.initial t)).ncard ≤ w) →
        Real.logb (Nat.card U) S.ncard ≤
          w + (r + 2) + 3 * Real.logb (Nat.card U) K +
            Real.logb (Nat.card U) (Nat.card V + 1) := by
  let N := constraintNetwork I Acc c
  let H := N.hide
  have hacc : H.accepted = S := by
    rw [Network.accepted_hide, Compiler.accepted_network]
    ext x
    rw [hS x]
    exact ⟨fun ⟨y, hy⟩ => ⟨y, hy 0⟩, fun ⟨y, hy⟩ =>
      ⟨y, fun o => Subsingleton.elim o 0 ▸ hy⟩⟩
  have hf : RectangleFree H.accepted K := hacc ▸ hfree
  have hb : Nat.card U * K ^ 2 ≤ H.accepted.ncard := hacc ▸ hbig
  have hread : N.read.ncard = H.read.ncard + (readWitnesses c).ncard := by
    simpa only [N, H, constraintNetwork, Compiler.read_network, readWitnesses, mem_ofPred_eq] using
      N.ncard_read_eq_hide_add
  have hrank := Compiler.cycleRank_add_ncard_read_le (out := c.outputs) I (fun _ => Acc) hfan
    (Compiler.connected I _)
  have hsum : H.cycleRank + H.read.ncard + (readWitnesses c).ncard ≤
      (r - 1) * c.innerSize + 1 := by
    change N.cycleRank + H.read.ncard + (readWitnesses c).ncard ≤ _
    rw [hread] at hrank
    simpa only [Circuit.innerSize, add_assoc] using hrank
  have hq : (1 : ℝ) < Nat.card U := by exact_mod_cast Finite.one_lt_card
  have hunread : (H.readᶜ.ncard : ℝ) < Real.logb (Nat.card U) K := by
    rw [Real.lt_logb_iff_rpow_lt hq (by exact_mod_cast hfree.pos), Real.rpow_natCast]
    exact_mod_cast hf.pow_ncard_compl_lt H.dependsOn_read hb
  have hcompl : H.readᶜ.ncard + H.read.ncard = n := by
    have h := ncard_add_ncard_compl H.read
    simpa [Nat.card_eq_fintype_card, add_comm] using h
  have hcycle : (H.cycleRank : ℝ) ≤
      ((r - 1) * c.innerSize : ℕ) - (readWitnesses c).ncard - n +
        Real.logb (Nat.card U) K + 1 := by
    have hs : (H.cycleRank : ℝ) + H.read.ncard + (readWitnesses c).ncard ≤
        ((r - 1) * c.innerSize : ℕ) + 1 := by
      exact_mod_cast hsum
    have hc : (H.readᶜ.ncard : ℝ) + H.read.ncard = n := by exact_mod_cast hcompl
    linarith
  refine ⟨_, _, inferInstance, inferInstance, H.toMultigraph,
    Compiler.connected I (fun _ => Acc), Compiler.loopless I (fun _ => Acc),
    Compiler.maxDegreeLE I (fun _ => Acc) hr hfan,
    ?_, hcycle, ?_⟩
  · simpa [Circuit.innerSize] using Compiler.card_vertex_le (out := c.outputs) hfan
  · intro π w hw
    have h := H.logb_ncard_accepted_le hf hb π hw
      (Compiler.maxDegreeLE I (fun _ => Acc) hr hfan)
      (fun v => (N.ncard_readAt_hide_le v).trans (Compiler.ncard_readAt_le I (fun _ => Acc) v))
    rw [hacc] at h
    convert h using 1
    push_cast
    ring

/-- The witness-independent reduction, obtained by dropping the nonnegative witness credit. -/
theorem exists_graph_of_nondeterministic_decides {I : Interpretation σ U} {Acc : Set U}
    {c : Circuit σ (n + k) 1} {S : Set (Fin n → U)} {K r : ℕ}
    (hr : 2 ≤ r) (hfan : c.FanInAtMost r) (hS : NondeterministicDecides c I Acc S)
    (hfree : RectangleFree S K) (hbig : Nat.card U * K ^ 2 ≤ S.ncard) :
    ∃ (V E : Type) (_ : Finite V) (_ : Finite E) (G : Multigraph V E),
      G.Connected ∧ G.Loopless ∧ G.MaxDegreeLE (r + 1) ∧
      Nat.card V ≤ 2 * r * c.innerSize + 3 ∧
      (G.cycleRank : ℝ) ≤ ((r - 1) * c.innerSize : ℕ) - n + Real.logb (Nat.card U) K + 1 ∧
      ∀ (π : Layout V) (w : ℕ), (∀ t, (G.cut (π.initial t)).ncard ≤ w) →
        Real.logb (Nat.card U) S.ncard ≤
          w + (r + 2) + 3 * Real.logb (Nat.card U) K +
            Real.logb (Nat.card U) (Nat.card V + 1) := by
  obtain ⟨V, E, _, _, G, hc, hl, hd, hV, hrank, hw⟩ :=
    exists_graph_of_nondeterministic_decides_witnesses hr hfan hS hfree hbig
  refine ⟨V, E, inferInstance, inferInstance, G, hc, hl, hd, hV, ?_, hw⟩
  linarith [Nat.cast_nonneg (α := ℝ) (readWitnesses c).ncard]

/-- The frontier lower bound for verifiers, uniformly in the number of existential inputs. -/
theorem lowerBound_nondeterministic {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost r → NondeterministicDecides c I Acc (S n) →
        (1 + 1 / A - ε) * n < (r - 1) * c.innerSize := by
  filter_upwards [lowerBound_of_graph hr hA hlayout S K hfree hK hdense hε,
    hfree, eventually_card_mul_sq_le_ncard S K hfree hK hdense] with n hn hf hb
  intro k σ I Acc c hfan hS
  obtain ⟨V, E, _, _, G, hc, hl, hd, hV, hrank, hw⟩ :=
    exists_graph_of_nondeterministic_decides hr hfan hS hf hb
  exact hn c.innerSize V E G hc hl hd hV hrank hw

/-- The Gaussian coefficient also holds for nondeterministic circuits of fan-in two. -/
theorem lowerBound_nondeterministic_gaussian (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.FanInAtMost 2 → NondeterministicDecides c I Acc (S n) →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n < c.innerSize := by
  have h := lowerBound_nondeterministic (r := 2) le_rfl
    (mul_pos two_pos Gaussian.gaussianCoefficient_pos) layoutBound_gaussian S K hfree hK hdense hε
  rw [Gaussian.one_add_inv_two_mul_gaussianCoefficient] at h
  norm_num at h ⊢
  exact h

/-- **Witness-sensitive lower bound.** For any fixed polynomial size bound, a verifier pays
one additional gate for every distinct witness input reachable from its output. A cubic
layout coefficient `p` gives gate coefficient `1 + 1 / (2p)`. The threshold is uniform in
the declared witness length, the gate basis, and the interpretation. -/
theorem lowerBound_nondeterministic_witnesses {p : ℝ} (hp : 0 < p)
    (hlayout : CubicLayoutBound p) (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ)) (D : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.innerSize ≤ n ^ D → c.FanInAtMost 2 →
        NondeterministicDecides c I Acc (S n) →
        (1 + 1 / (2 * p) - ε) * n + (readWitnesses c).ncard < c.innerSize := by
  set q := Nat.card U
  have hq : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  have hlogq_pos : 0 < Real.log q := Real.log_pos hq
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨η, hη, H⟩ := eventually_lt_of_linear_demand (mul_pos two_pos hp) hε
  obtain ⟨C, hC⟩ := hlayout.exists_layout_log hp.le hη
  -- The graph has polynomial size, so both logarithmic overheads are `o(n)`.
  set e : ℕ → ℝ := fun n =>
    (n - Real.logb q (S n).ncard) + (2 * p + η + 3) * Real.logb q (K n) +
      (3 / Real.log 2 + 1 / Real.log q) * Real.log (4 * (n : ℝ) ^ D + 4) +
      (2 * p + η + 4 + C)
  have hk : (fun n => Real.logb q (K n)) =o[atTop] fun n => (n : ℝ) := by
    simpa only [Real.logb, div_eq_mul_inv, one_mul, mul_comm] using
      hK.const_mul_left (1 / Real.log q)
  have hlog_size : (fun n : ℕ => Real.log (4 * (n : ℝ) ^ D + 4)) =o[atTop]
      fun n => (n : ℝ) := isLittleO_log_polynomial D (by positivity) (by norm_num)
  have hconstant : (fun _ : ℕ => 2 * p + η + 4 + C) =o[atTop] fun n => (n : ℝ) :=
    isLittleO_const_left.mpr (Or.inr
      (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop))
  -- Density loss, rectangle threshold, logarithmic graph overhead, and a constant.
  have he : e =o[atTop] fun n => (n : ℝ) :=
    (((isLittleO_sub_logb_ncard S hdense).add (hk.const_mul_left _)).add
      (hlog_size.const_mul_left _)).add hconstant
  filter_upwards [H e he, hfree, eventually_card_mul_sq_le_ncard S K hfree hK hdense]
    with n hn hf hb
  intro k σ I Acc c hsize hfan hS
  obtain ⟨V, E, _, _, G, hc, _, hd, hV, hrank, hw⟩ :=
    exists_graph_of_nondeterministic_decides_witnesses le_rfl hfan hS hf hb
  norm_num only [Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, one_mul] at hd hV hrank hw
  obtain ⟨π, hπ⟩ := hC V E G hc hd
  set B := (2 * p + η) * G.cycleRank + 3 * Nat.log 2 (Nat.card V) + C
  have hB : 0 ≤ B := by simpa [Layout.initial_zero] using hπ 0
  have hwidth := hw π ⌊B⌋₊ fun t => Nat.le_floor (hπ t)
  have hfloor : (⌊B⌋₊ : ℝ) ≤
      (2 * p + η) * G.cycleRank + 3 * Nat.log 2 (Nat.card V) + C := Nat.floor_le hB
  have hVs : (Nat.card V : ℝ) + 1 ≤ 4 * (n : ℝ) ^ D + 4 := by
    have : Nat.card V + 1 ≤ 4 * n ^ D + 4 := by lia
    exact_mod_cast this
  have hlogV : Real.log ((Nat.card V : ℝ) + 1) ≤ Real.log (4 * (n : ℝ) ^ D + 4) :=
    Real.log_le_log (by positivity) hVs
  have hlogq : Real.logb q ((Nat.card V : ℝ) + 1) ≤
      Real.log (4 * (n : ℝ) ^ D + 4) / Real.log q := by
    exact div_le_div_of_nonneg_right hlogV hlogq_pos.le
  have hlog2 : (Nat.log 2 (Nat.card V) : ℝ) ≤
      Real.log (4 * (n : ℝ) ^ D + 4) / Real.log 2 := by
    calc (Nat.log 2 (Nat.card V) : ℝ)
        ≤ Real.logb 2 (Nat.card V + 1 : ℕ) :=
          (Nat.cast_le.mpr (Nat.log_mono_right (Nat.le_succ _))).trans
            (Real.natLog_le_logb _ _)
      _ = Real.log ((Nat.card V : ℝ) + 1) / Real.log 2 := by simp [Real.logb]
      _ ≤ _ := div_le_div_of_nonneg_right hlogV hlog2_pos.le
  have hsupply := mul_le_mul_of_nonneg_left hrank (show 0 ≤ 2 * p + η by positivity)
  have hbudget := hn ((c.innerSize : ℝ) - (readWitnesses c).ncard) (by
    dsimp only [e, q]
    dsimp only [q] at hlogq
    simp only [div_eq_mul_inv] at hlogq hlog2 ⊢
    nlinarith only [hwidth, hfloor, hlogq, hlog2, hsupply])
  linarith

/-- **Gaussian witness charge.** A verifier of size at most `n^D` computing a dense
rectangle-free family has more than `(4.562497… - ε)n + |read witnesses|` inner gates. -/
theorem lowerBound_nondeterministic_witnesses_gaussian (S : ∀ n, Set (Fin n → U)) (K : ℕ → ℕ)
    (hfree : ∀ᶠ n in atTop, RectangleFree (S n) (K n))
    (hK : (fun n => Real.log (K n)) =o[atTop] fun n => (n : ℝ))
    (hdense : (fun n => n * Real.log (Nat.card U) - Real.log (S n).ncard) =o[atTop]
      fun n => (n : ℝ)) (D : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (k : ℕ) (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ (n + k) 1), c.innerSize ≤ n ^ D → c.FanInAtMost 2 →
        NondeterministicDecides c I Acc (S n) →
        (1 + Real.pi / (3 * Real.arccos ((1 + 2 * Real.sqrt 2) / 4)) - ε) * n +
          (readWitnesses c).ncard < c.innerSize := by
  have h := lowerBound_nondeterministic_witnesses Gaussian.gaussianCoefficient_pos
    Gaussian.cubicLayoutBound_gaussian S K hfree hK hdense D hε
  rwa [Gaussian.one_add_inv_two_mul_gaussianCoefficient] at h

end Frontier
