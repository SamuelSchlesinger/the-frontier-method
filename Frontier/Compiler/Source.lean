/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Compiler
public import Frontier.Layouts.SourceForest

/-!
# Sources of the compiled network

A topological rank increases on every directed compiled edge, including the
fanout junction chains. When reachable gates have positive arity, the only
vertices without an incoming edge are input vertices. Consequently the
one-source blocks of every compression induce a forest, and a final cubic
compression has at least `h/2-r` such blocks.

These are structural supply lemmas. They do not assert an improved layout
bound or preservation of the full coefficient under redundant parity inputs.
-/

@[expose] public section

namespace Frontier.Compiler

open Cslib.Circuits Finset

variable {σ : Signature} {n s : ℕ} {O : Type*} [Finite O]
  (p : Program σ n s) (out : O → Wire n s)

/-- Inputs precede gates in program order. -/
def wireLevel : Wire n s → ℕ
  | .input _ => 0
  | .gate g => g.val + 1

private theorem wireLevel_le (w : Wire n s) : wireLevel w ≤ s := by
  cases w with
  | input => simp [wireLevel]
  | gate g => have := g.isLt; simp only [wireLevel]; lia

private theorem wireLevel_arg_lt (g : Fin s) (a : Fin (σ.Arity (p.lines g).op)) :
    wireLevel ((p.lines g).wires a) < g.val + 1 := by
  generalize hw : (p.lines g).wires a = w
  cases w with
  | input => simp [wireLevel]
  | gate g' =>
    have := p.lines_wires_eq_gate_lt g a hw
    simp only [wireLevel]
    exact Nat.add_lt_add_right this 1

/-- Space between consecutive program levels accommodates every junction chain. -/
noncomputable def topologicalRank : Vertex p out → ℕ
  | .signal w => wireLevel w.val * (Nat.card (Consumer p out) + 1)
  | .junction j => wireLevel j.1.val * (Nat.card (Consumer p out) + 1) + j.2.val + 1
  | .output _ => (s + 1) * (Nat.card (Consumer p out) + 1)

/-- Every directed edge of the compiled network increases the topological rank. -/
theorem topologicalRank_src_lt_tgt (e : Edge p out) :
    topologicalRank p out (src e) < topologicalRank p out (tgt e) := by
  let M := Nat.card (Consumer p out) + 1
  have hM : 0 < M := by dsimp [M]; lia
  have hjbound : ∀ j : Junction p out, j.2.val + 1 < M := by
    intro j
    have hcard : fanout p out j.1 ≤ Nat.card (Consumer p out) :=
      Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    have := j.2.isLt
    dsimp [M]
    lia
  cases e with
  | feed j =>
    simp only [src, tgt, feeder]
    split_ifs with hj <;> simp only [topologicalRank]
    · lia
    · have := j.2.isLt; lia
  | deliver j =>
    have hj := hjbound j
    rcases hc : junctionEquiv p out j with a | o
    · have hw : j.1.val = (p.lines a.1.1).wires a.1.2 := by
        have := congrArg Subtype.val (consumed_junctionEquiv j)
        simpa [hc, consumed] using this.symm
      have hlev := wireLevel_arg_lt p a.1.1 a.1.2
      have hmul := Nat.mul_le_mul_right M (Nat.succ_le_iff.mpr hlev)
      simp only [src, tgt, hc, owner, topologicalRank, wireLevel]
      rw [hw]
      change wireLevel ((p.lines a.1.1).wires a.1.2) * M + j.2.val + 1 <
        (a.1.1.val + 1) * M
      nlinarith
    · have hmul := Nat.mul_le_mul_right M (wireLevel_le j.1.val)
      simp only [src, tgt, hc, owner, topologicalRank]
      change wireLevel j.1.val * M + j.2.val + 1 < (s + 1) * M
      nlinarith

/-- The reachable input indices. -/
abbrev InputSignal : Type := {i : Fin n // Reach p out (.input i)}

/-- Input sites, counted as vertices of the compiled network. -/
noncomputable def inputVertices : Finset (Vertex p out) := by
  classical
  exact univ.image fun i : InputSignal p out => .signal ⟨.input i.val, i.property⟩

omit [Finite O] in
theorem mem_inputVertices {v : Vertex p out} : v ∈ inputVertices p out ↔
    ∃ i : InputSignal p out, v = .signal ⟨.input i.val, i.property⟩ := by
  classical
  simp [inputVertices, eq_comm]

omit [Finite O] in
theorem card_inputVertices : (inputVertices p out).card = Nat.card (InputSignal p out) := by
  classical
  rw [inputVertices, card_image_of_injective _ (by
    intro i j h
    exact Subtype.ext (Wire.input.inj (congrArg Subtype.val (Vertex.signal.inj h)))),
    card_univ, Nat.card_eq_fintype_card]

/-- With no reachable constant gates, every non-input vertex has an incoming edge. -/
theorem input_or_incoming
    (hnonzero : ∀ g, Reach p out (.gate g) → σ.Arity (p.lines g).op ≠ 0)
    (v : Vertex p out) : v ∈ inputVertices p out ∨ ∃ e, tgt e = v := by
  cases v with
  | signal w =>
    obtain ⟨w, hw⟩ := w
    cases w with
    | input i => exact Or.inl ((mem_inputVertices p out).mpr ⟨⟨i, hw⟩, rfl⟩)
    | gate g =>
      exact Or.inr ⟨argEdge hw ⟨0, Nat.pos_of_ne_zero (hnonzero g hw)⟩, tgt_argEdge ..⟩
  | junction j => exact Or.inr ⟨.feed j, rfl⟩
  | output o => exact Or.inr ⟨outEdge o, tgt_outEdge o⟩

variable {A : Type*} (I : Interpretation σ A) (Acc : O → Set A)

/-- A reachable zero-arity gate would carry a constant signal. -/
theorem arity_ne_zero_of_nonconstant
    (hnonconst : ∀ e : Edge p out, ∃ x y,
      p.trace I x e.signal.val ≠ p.trace I y e.signal.val)
    (g : Fin s) (hg : Reach p out (.gate g)) : σ.Arity (p.lines g).op ≠ 0 := by
  intro hzero
  obtain ⟨x, y, hxy⟩ := hnonconst (head ⟨.gate g, hg⟩)
  apply hxy
  change p.trace I x (.gate g) = p.trace I y (.gate g)
  rw [p.trace_gate, p.trace_gate]
  congr 1
  funext a
  have := a.isLt
  lia

/-- Input equality and incoming trace equality determine every outgoing value
at a compiler vertex. This holds on all inputs, independently of acceptance. -/
theorem trace_local {x y : Fin n → A} (v : Vertex p out)
    (hinput : ∀ i (hi : Reach p out (.input i)),
      v = .signal ⟨.input i, hi⟩ → x i = y i)
    (hin : ∀ e, tgt e = v → p.trace I x e.signal.val = p.trace I y e.signal.val) :
    ∀ e, src e = v → p.trace I x e.signal.val = p.trace I y e.signal.val := by
  cases v with
  | signal w =>
    intro e he
    rw [eq_head_of_src_eq_signal he]
    obtain ⟨w, hw⟩ := w
    cases w with
    | input i => exact hinput i hw rfl
    | gate g =>
      simp only [head, Edge.signal, p.trace_gate]
      congr 1
      funext a
      simpa using hin (argEdge hw a) (tgt_argEdge hw a)
  | junction j =>
    intro e he
    rw [signal_of_src_eq_junction he]
    exact hin (.feed j) rfl
  | output o =>
    intro e he
    cases e with
    | feed j =>
      simp only [src, feeder] at he
      split_ifs at he
    | deliver j => cases he

/-- All values in a block are determined by its original inputs and entering
edges, even when the orientation of the quotient contains a cycle. -/
theorem trace_eqOn_block {d : ℕ}
    (c : Multigraph.Compression (network p out I Acc).toMultigraph d) (B : c.blocks)
    {x y : Fin n → A}
    (hinput : ∀ i (hi : Reach p out (.input i)),
      c.blockOf (.signal ⟨.input i, hi⟩) = B → x i = y i)
    (hin : ∀ e ∈ c.incoming B, p.trace I x e.signal.val = p.trace I y e.signal.val) :
    ∀ e, c.blockOf (src e) = B ∨ c.blockOf (tgt e) = B →
      p.trace I x e.signal.val = p.trace I y e.signal.val := by
  have hout := c.eqOn_block (topologicalRank p out) (topologicalRank_src_lt_tgt p out) B
    (fun e => p.trace I x e.signal.val) (fun e => p.trace I y e.signal.val)
    (fun v hv => trace_local p out I v (fun i hi h => hinput i hi (h ▸ hv))) hin
  intro e he
  by_cases hs : c.blockOf (src e) = B
  · exact hout e hs
  · exact hin e ((c.mem_incoming B e).mpr ⟨hs, he.resolve_left hs⟩)

/-- A block with one source has all its incident edge values determined by a
single alphabet value. The source can be an entering edge or an original input. -/
theorem oneSource_determines {d : ℕ}
    (c : Multigraph.Compression (network p out I Acc).toMultigraph d) (B : c.blocks)
    (hload : c.sourceLoad (inputVertices p out) B = 1) :
    ∃ value : (Fin n → A) → A, ∀ x y, value x = value y →
      ∀ e, c.blockOf (src e) = B ∨ c.blockOf (tgt e) = B →
        p.trace I x e.signal.val = p.trace I y e.signal.val := by
  classical
  let inputs := (inputVertices p out).filter fun v => c.blockOf v = B
  have hsum : (c.incoming B).card + inputs.card = 1 := hload
  by_cases hin : (c.incoming B).Nonempty
  · obtain ⟨e₀, he₀⟩ := hin
    have hpos := card_pos.mpr ⟨e₀, he₀⟩
    have hcard : (c.incoming B).card ≤ 1 := by lia
    have hempty : inputs = ∅ := card_eq_zero.mp (by lia)
    refine ⟨fun x => p.trace I x e₀.signal.val, fun x y hxy =>
      trace_eqOn_block p out I Acc c B ?_ ?_⟩
    · intro i hi hB
      have hmem : Vertex.signal (p := p) (out := out) ⟨.input i, hi⟩ ∈ inputs :=
        mem_filter.mpr ⟨(mem_inputVertices p out).mpr ⟨⟨i, hi⟩, rfl⟩, hB⟩
      simp [hempty] at hmem
    · intro e he
      simpa only [card_le_one.mp hcard e he e₀ he₀] using hxy
  · have hempty : c.incoming B = ∅ := not_nonempty_iff_eq_empty.mp hin
    have hcard : inputs.card = 1 := by simp only [hempty, card_empty, zero_add] at hsum; exact hsum
    obtain ⟨v, hv⟩ := card_pos.mp (show 0 < inputs.card by lia)
    obtain ⟨hvinput, hvB⟩ := mem_filter.mp hv
    obtain ⟨i, rfl⟩ := (mem_inputVertices p out).mp hvinput
    refine ⟨fun x => x i.val, fun x y hxy => trace_eqOn_block p out I Acc c B ?_ ?_⟩
    · intro j hj hB
      have hmem : Vertex.signal (p := p) (out := out) ⟨.input j, hj⟩ ∈ inputs :=
        mem_filter.mpr ⟨(mem_inputVertices p out).mpr ⟨⟨j, hj⟩, rfl⟩, hB⟩
      have heq := card_le_one.mp hcard.le _ hmem _ hv
      have hij := Wire.input.inj (congrArg Subtype.val (Vertex.signal.inj heq))
      simpa only [hij] using hxy
    · simp [hempty]

/-- Boolean ports of a one-source block are functions of one bit, with no
assumption about which direction the eventual sweep crosses the block. -/
theorem oneSource_ports (I : Interpretation σ Bool) (Acc : O → Set Bool) {d : ℕ}
    (c : Multigraph.Compression (network p out I Acc).toMultigraph d) (B : c.blocks)
    (hload : c.sourceLoad (inputVertices p out) B = 1) :
    ∃ value : (Fin n → Bool) → Bool, ∃ port : Bool → Edge p out → Bool,
      ∀ x e, c.blockOf (src e) = B ∨ c.blockOf (tgt e) = B →
        p.trace I x e.signal.val = port (value x) e := by
  classical
  obtain ⟨value, hvalue⟩ := oneSource_determines p out I Acc c B hload
  let f : (Fin n → Bool) → Edge p out → Bool := fun x e =>
    if c.blockOf (src e) = B ∨ c.blockOf (tgt e) = B then p.trace I x e.signal.val else false
  have hf : f.FactorsThrough value := by
    intro x y hxy
    funext e
    dsimp [f]
    split_ifs with he
    · exact hvalue x y hxy e he
    · rfl
  obtain ⟨port, hport⟩ := (Function.factorsThrough_iff f).mp hf
  refine ⟨value, port, fun x e he => ?_⟩
  have h := congrFun (congrFun hport x) e
  simpa only [f, ite_eq_left he, Function.comp_apply] using h

/-- Two nonconstant ports of a one-source Boolean block are equal or
complementary, even if other ports of the block are constant. -/
theorem oneSource_xor_of_nonconstant (I : Interpretation σ Bool) (Acc : O → Set Bool) {d : ℕ}
    (c : Multigraph.Compression (network p out I Acc).toMultigraph d) (B : c.blocks)
    (hload : c.sourceLoad (inputVertices p out) B = 1)
    (x y : Fin n → Bool) (e e' : Edge p out)
    (he : c.blockOf (src e) = B ∨ c.blockOf (tgt e) = B)
    (he' : c.blockOf (src e') = B ∨ c.blockOf (tgt e') = B)
    (hne : ∃ u v, p.trace I u e.signal.val ≠ p.trace I v e.signal.val)
    (hne' : ∃ u v, p.trace I u e'.signal.val ≠ p.trace I v e'.signal.val) :
    Bool.xor (p.trace I x e.signal.val) (p.trace I y e.signal.val) =
      Bool.xor (p.trace I x e'.signal.val) (p.trace I y e'.signal.val) := by
  obtain ⟨value, port, hport⟩ := oneSource_ports p out I Acc c B hload
  have hport_ne : ∀ e, (c.blockOf (src e) = B ∨ c.blockOf (tgt e) = B) →
      (∃ u v, p.trace I u e.signal.val ≠ p.trace I v e.signal.val) →
      port false e ≠ port true e := by
    rintro e he ⟨u, v, huv⟩ h
    apply huv
    rw [hport u e he, hport v e he]
    cases value u <;> cases value v <;> simp_all
  have hxor : ∀ e, port false e ≠ port true e → ∀ a b,
      Bool.xor (port a e) (port b e) = Bool.xor a b := by
    intro e h a b
    cases a <;> cases b <;> cases hf : port false e <;> cases ht : port true e <;> simp_all
  rw [hport x e he, hport y e he, hport x e' he', hport y e' he',
    hxor e (hport_ne e he hne), hxor e' (hport_ne e' he' hne')]

/-- Nonconstant signals on a one-source Boolean block are equal or complementary.
Thus the XOR difference of any two traces is constant over its incident edges. -/
theorem oneSource_xor (I : Interpretation σ Bool) (Acc : O → Set Bool) {d : ℕ}
    (c : Multigraph.Compression (network p out I Acc).toMultigraph d) (B : c.blocks)
    (hload : c.sourceLoad (inputVertices p out) B = 1)
    (hnonconst : ∀ e, c.blockOf (src e) = B ∨ c.blockOf (tgt e) = B →
      ∃ x y, p.trace I x e.signal.val ≠ p.trace I y e.signal.val)
    (x y : Fin n → Bool) (e e' : Edge p out)
    (he : c.blockOf (src e) = B ∨ c.blockOf (tgt e) = B)
    (he' : c.blockOf (src e') = B ∨ c.blockOf (tgt e') = B) :
    Bool.xor (p.trace I x e.signal.val) (p.trace I y e.signal.val) =
      Bool.xor (p.trace I x e'.signal.val) (p.trace I y e'.signal.val) :=
  oneSource_xor_of_nonconstant p out I Acc c B hload x y e e' he he'
    (hnonconst e he) (hnonconst e' he')

/-- The compiled circuit supplies the forest hypothesis, without assuming that
the full quotient preserves its directed acyclicity. -/
theorem oneSource_acyclic {d : ℕ}
    (c : Multigraph.Compression (network p out I Acc).toMultigraph d)
    (hnonzero : ∀ g, Reach p out (.gate g) → σ.Arity (p.lines g).op ≠ 0) :
    (c.quotient.induce {B | c.sourceLoad (inputVertices p out) B = 1}).IsAcyclic :=
  c.oneSource_acyclic (topologicalRank p out) (topologicalRank_src_lt_tgt p out)
    (inputVertices p out) (input_or_incoming p out hnonzero)

/-- In a connected final cubic core, `h ≤ 2(|U|+r)`, where `U` is the forest of
one-source blocks and `r` is the number of reached circuit inputs. -/
theorem card_le_twice_oneSource_add_inputs
    (c : Multigraph.Compression (network p out I Acc).toMultigraph)
    (hc : c.Final) (hconn : (network p out I Acc).Connected) (two : 2 ≤ c.blocks.card)
    (hnonzero : ∀ g, Reach p out (.gate g) → σ.Arity (p.lines g).op ≠ 0) :
    c.blocks.card ≤ 2 * ((univ.filter fun B => c.sourceLoad (inputVertices p out) B = 1).card +
      Nat.card (InputSignal p out)) := by
  simpa only [card_inputVertices] using
    c.card_le_twice_oneSource_add_sources hc hconn two (topologicalRank p out)
      (topologicalRank_src_lt_tgt p out) (inputVertices p out) (input_or_incoming p out hnonzero)

end Frontier.Compiler
