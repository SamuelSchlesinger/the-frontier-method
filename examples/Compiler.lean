/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Frontier.Compiler
import Mathlib.Tactic.FinCases

/-! # A circuit, its compiled graph, and an output-side frontier

This is the complete example in `paper/frontier.tex`: `a = x₁ xor x₂`,
`b = a xor x₃`, `c = a or b`, accepting when `c = true`. Lean indexes inputs and gates from
zero. Gate `a` is shared, so this is a circuit rather than a read-once formula.

Run after `lake build --wfail`:
`lake env lean -DwarningAsError=true examples/Compiler.lean`.
-/

namespace Frontier.Examples

open Cslib.Circuits Compiler Set

inductive Op where
  | xor | or

abbrev signature : Signature where
  Op := Op
  Arity := fun _ => 2

def interpretation : Interpretation signature Bool
  | .xor, x => x 0 ^^ x 1
  | .or, x => x 0 || x 1

/-- Each line can use only the original inputs and earlier gates. -/
def program : Program signature 3 3 :=
  .gate (.gate (.gate .empty
    ⟨.xor, ![.input 0, .input 1]⟩)
    ⟨.xor, ![.gate 0, .input 2]⟩)
    ⟨.or, ![.gate 0, .gate 1]⟩

def output : Unit → Wire 3 3 := fun _ => .gate 2

def circuit : Circuit signature 3 1 := ⟨program, fun _ => output ()⟩

example : circuit.FanInAtMost 2 := by decide
example : circuit.innerSize = 3 := by decide

/-- The independent Boolean expression against which to check circuit semantics. -/
def acceptedInput (x : Fin 3 → Bool) : Prop :=
  ((x 0 ^^ x 1) || ((x 0 ^^ x 1) ^^ x 2)) = true

example (x : Fin 3 → Bool) : circuit.eval interpretation x 0 = true ↔ acceptedInput x :=
  Iff.rfl

noncomputable def net : Network Bool (Fin 3) (Vertex program output) (Edge program output) :=
  network program output interpretation (fun _ => {true})

/-- The general exactness theorem identifies the accepted inputs. -/
theorem accepted_net : net.accepted = {x | acceptedInput x} := by
  rw [net, accepted_network]
  ext x
  change (∀ _ : Unit, acceptedInput x) ↔ acceptedInput x
  simp

/-- All six wires are reachable, including the shared gate `a`. -/
theorem reachable (w : Wire 3 3) : Reach program output w := by
  have hc : Reach program output (.gate 2) := .out ()
  have ha : Reach program output (.gate 0) := .arg (g := 2) 0 hc
  have hb : Reach program output (.gate 1) := .arg (g := 2) 1 hc
  cases w with
  | gate g => fin_cases g <;> assumption
  | input i =>
    fin_cases i
    · exact Reach.arg (g := 0) 0 ha
    · exact Reach.arg (g := 0) 1 ha
    · exact Reach.arg (g := 1) 1 hb

theorem signals : Nat.card (Signal program output) = 6 := by
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv reachable), Nat.card_eq_fintype_card]
  decide

theorem slots : Nat.card (Slot program output) = 6 := by
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv
    (fun t : Σ g : Fin 3, Fin (signature.Arity (program.lines g).op) => reachable (.gate t.1)))]
  rw [Nat.card_eq_fintype_card]
  decide

theorem consumers : Nat.card (Consumer program output) = 7 := by
  rw [card_consumer, slots]
  simp

example : Nat.card (Junction program output) = 7 := by
  rw [Nat.card_congr (junctionEquiv program output), consumers]

theorem vertices : Nat.card (Vertex program output) = 14 := by
  rw [card_vertex, signals, consumers]
  simp

theorem edges : Nat.card (Edge program output) = 14 := by rw [card_edge, consumers]

example : net.Connected := connected interpretation (fun _ => {true})
example : net.cycleRank = 1 := by simp [Multigraph.cycleRank, vertices, edges]
example : net.MaxDegreeLE 3 := maxDegreeLE interpretation (fun _ => {true}) (by decide)
  (show program.FanInAtMost 2 by decide)

/-- Process the output gate `c`, its copying junctions, and the output vertex first.
This is a valid prefix of some ordering, even though no input vertex is present. -/
def processed : Set (Vertex program output)
  | .signal w => w.1 = .gate 2
  | .junction j => j.1.1 = .gate 2
  | .output _ => True

/-- The two edges entering `c`, carrying the values of `a` and `b`. -/
noncomputable def entering (i : Fin 2) : Edge program output :=
  argEdge (reachable (.gate 2)) i

theorem processed_cut (e : Edge program output) :
    e ∈ net.cut processed ↔ e = entering 0 ∨ e = entering 1 := by
  change (¬(processed (src e) ↔ processed (tgt e))) ↔ _
  cases e with
  | feed j =>
    simp only [src, tgt, feeder]
    split_ifs <;> simp [processed, entering, argEdge]
  | deliver j =>
    obtain ⟨consumer, rfl⟩ := (junctionEquiv program output).symm.surjective j
    rcases consumer with ⟨⟨g, a⟩, hg⟩ | o
    · fin_cases g <;> fin_cases a <;>
        simp only [src, tgt, Equiv.apply_symm_apply, processed, owner,
          fst_junctionEquiv_symm, consumed, entering, argEdge, Edge.deliver.injEq,
          (junctionEquiv program output).symm.injective.eq_iff, Sum.inl.injEq,
          Subtype.mk.injEq]
      all_goals decide
    · cases o
      simp [src, tgt, processed, owner, entering, argEdge, consumed, output,
        (junctionEquiv program output).symm.injective.eq_iff]

theorem entering_injective : Function.Injective entering := by
  intro i j h
  have h' := congrArg (fun e => match e with
    | .deliver j => some (junctionEquiv program output j)
    | .feed _ => none) h
  simpa [entering, argEdge] using h'

example : (net.cut processed).ncard = 2 := by
  have hcut : net.cut processed = Set.range entering := by
    ext e
    rw [processed_cut]
    simp only [Set.mem_range]
    constructor
    · rintro (rfl | rfl) <;> exact ⟨_, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  rw [hcut, Set.ncard_range_of_injective entering_injective]
  simp

theorem processed_reads : net.readIn processed = ∅ := by
  ext i
  change (∃ v ∈ processed, Compiler.site (p := program) (out := output) i = some v) ↔ False
  rw [site_of_reach (reachable (.input i))]
  constructor
  · rintro ⟨v, hv, heq⟩
    cases Option.some.inj heq
    change (Wire.input i : Wire 3 3) = .gate 2 at hv
    cases hv
  · exact False.elim

/-- Both inputs are accepted, although the frontier values differ before any input is read. -/
example : (![false, false, true] : Fin 3 → Bool) ∈ net.accepted := by
  rw [accepted_net]
  change acceptedInput _
  rfl

example : (![true, false, false] : Fin 3 → Bool) ∈ net.accepted := by
  rw [accepted_net]
  change acceptedInput _
  rfl

example : (fun i => program.trace interpretation ![false, false, true] (entering i).signal.1) =
    ![false, true] := by
  funext i
  simp only [entering, signal_argEdge]
  fin_cases i <;> rfl

example : (fun i => program.trace interpretation ![true, false, false] (entering i).signal.1) =
    ![true, true] := by
  funext i
  simp only [entering, signal_argEdge]
  fin_cases i <;> rfl

/-- The frontier value is not determined by the inputs read on the processed side. -/
example : ¬DependsOn (fun x => program.trace interpretation x (entering 0).signal.1)
    (net.readIn processed) := by
  rw [processed_reads]
  intro h
  have H : program.trace interpretation ![false, false, true] (entering 0).signal.1 =
      program.trace interpretation ![true, false, false] (entering 0).signal.1 := h (by simp)
  simp only [entering, signal_argEdge] at H
  exact Bool.false_ne_true H

end Frontier.Examples
