/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.ForCslib.Program
public import Cslib.Computability.Circuit.Composition
import Mathlib.Tactic

/-!
# Fixing Boolean circuit inputs

`Circuit.fixInputs` replaces a suffix of input ports by Boolean constants. It preserves
the number of positive-arity gates and the fan-in bound. The signature is extended by two
nullary operations, so no assumption that the original basis contains constants is needed.
-/

@[expose] public section

namespace Cslib.Circuits

universe v

variable {σ : Signature.{v}} {n k m s : ℕ}

/-- Appending a line costs one inner gate exactly when its operation has positive arity. -/
theorem Program.card_innerGates_gate (p : Program σ n s) (line : Line σ n s) :
    (p.gate line).innerGates.card = p.innerGates.card + if σ.Arity line.op = 0 then 0 else 1 := by
  simp only [Program.innerGates, Finset.card_filter]
  rw [Fin.sum_univ_castSucc]
  simp [Program.lines_gate_last, Program.lines_gate_castSucc]

/-- Wiring one program into another adds their positive-arity gate counts. -/
theorem Program.card_innerGates_append {g t : ℕ} (p : Program σ n g)
    (feed : Fin k → Wire n g) (q : Program σ k t) :
    (p.append feed q).innerGates.card = p.innerGates.card + q.innerGates.card := by
  induction q with
  | empty => exact (Nat.add_zero _).symm
  | gate q line ih =>
    simp only [Program.append, Program.card_innerGates_gate, Line.mapWires_op, ih]
    lia

/-- Wiring programs together does not change their gate arities. -/
theorem Program.FanInAtMost.append {g t r : ℕ} {p : Program σ n g} {q : Program σ k t}
    (hp : p.FanInAtMost r) (hq : q.FanInAtMost r) (feed : Fin k → Wire n g) :
    (p.append feed q).FanInAtMost r := by
  induction q with
  | empty => exact hp
  | gate q line ih => exact ⟨ih hq.1, hq.2⟩

/-- Adjoin Boolean constants to an arbitrary gate basis. -/
def Signature.withBoolConstants (σ : Signature) : Signature where
  Op := σ.Op ⊕ Bool
  Arity := Sum.elim σ.Arity (fun _ => 0)

/-- Extend an interpretation by the two nullary Boolean operations. -/
def Interpretation.withBoolConstants (I : Interpretation σ Bool) :
    Interpretation σ.withBoolConstants Bool
  | .inl op => I op
  | .inr b => fun _ => b

/-- Regard the original program as a program over the extended basis. -/
def Program.withBoolConstants {s : ℕ} : Program σ n s → Program σ.withBoolConstants n s
  | .empty => .empty
  | .gate p line => p.withBoolConstants.gate ⟨.inl line.op, line.wires⟩

theorem Program.arity_lines_withBoolConstants (p : Program σ n s) (g : Fin s) :
    σ.withBoolConstants.Arity (p.withBoolConstants.lines g).op = σ.Arity (p.lines g).op := by
  induction p with
  | empty => exact g.elim0
  | gate p line ih =>
    refine Fin.lastCases ?_ (fun g => ?_) g
    · simp only [Program.withBoolConstants, Program.lines_gate_last, Line.mapWires_op]
      rfl
    · simpa [Program.withBoolConstants, Program.lines_gate_castSucc] using ih g

@[simp] theorem Program.innerGates_withBoolConstants (p : Program σ n s) :
    p.withBoolConstants.innerGates = p.innerGates :=
  Finset.filter_congr fun g _ => by rw [Program.arity_lines_withBoolConstants]

theorem Program.FanInAtMost.withBoolConstants {p : Program σ n s} {r : ℕ}
    (h : p.FanInAtMost r) : p.withBoolConstants.FanInAtMost r := by
  induction p with
  | empty => trivial
  | gate p line ih => exact ⟨ih h.1, h.2⟩

@[simp] theorem Program.trace_withBoolConstants (p : Program σ n s)
    (I : Interpretation σ Bool) (x : Fin n → Bool) (w : Wire n s) :
    p.withBoolConstants.trace I.withBoolConstants x w = p.trace I x w := by
  induction p with
  | empty => cases w with
    | input => rfl
    | gate g => exact g.elim0
  | gate p line ih =>
    cases w with
    | input => rfl
    | gate g =>
      refine Fin.lastCases ?_ (fun g => ?_) g
      · simp only [Program.withBoolConstants, Program.trace, Wire.elim,
          Program.eval_gate_last, Line.eval, Interpretation.withBoolConstants]
        congr 1
        funext a
        exact ih (line.wires a)
      · simpa only [Program.withBoolConstants, Program.trace, Wire.elim,
          Program.eval_gate_castSucc] using ih (.gate g)

/-- The two constant wires used when fixing Boolean inputs. -/
def Program.boolConstants (σ : Signature) (n : ℕ) : Program σ.withBoolConstants n 2 :=
  ((Program.empty : Program σ.withBoolConstants n 0).gate
    ⟨Sum.inr false, Fin.elim0⟩).gate ⟨Sum.inr true, Fin.elim0⟩

/-- The original input ports followed by the chosen constant wires. -/
def Circuit.fixedInputWires (y : Fin k → Bool) : Fin (n + k) → Wire n 2 :=
  Fin.addCases Wire.input (fun j => .gate (if y j then 1 else 0))

/-- Fix the last `k` input ports to `y`. The added constant gates have zero cost in `innerSize`. -/
def Circuit.fixInputs (c : Circuit σ (n + k) m) (y : Fin k → Bool) :
    Circuit σ.withBoolConstants n m where
  program := (Program.boolConstants σ n).append (Circuit.fixedInputWires y)
    c.program.withBoolConstants
  outputs := Program.appendedWire (Circuit.fixedInputWires y) ∘ c.outputs

@[simp] theorem Circuit.innerSize_fixInputs (c : Circuit σ (n + k) m) (y : Fin k → Bool) :
    (c.fixInputs y).innerSize = c.innerSize := by
  simp only [Circuit.innerSize, Circuit.fixInputs, Program.card_innerGates_append,
    Program.innerGates_withBoolConstants, Program.boolConstants, Program.card_innerGates_gate]
  simp [Signature.withBoolConstants, Program.innerGates]

theorem Circuit.FanInAtMost.fixInputs {c : Circuit σ (n + k) m} {r : ℕ}
    (h : c.FanInAtMost r) (y : Fin k → Bool) : (c.fixInputs y).FanInAtMost r := by
  apply Program.FanInAtMost.append _ h.withBoolConstants
  simp [Program.boolConstants, Program.FanInAtMost, Signature.withBoolConstants]

@[simp] theorem Circuit.eval_fixInputs (c : Circuit σ (n + k) m)
    (I : Interpretation σ Bool) (y : Fin k → Bool) (x : Fin n → Bool) :
    (c.fixInputs y).eval I.withBoolConstants x = c.eval I (Fin.append x y) := by
  have hfeed : (fun i => (Program.boolConstants σ n).trace I.withBoolConstants x
      (Circuit.fixedInputWires y i)) =
      Fin.append x y := by
    funext i
    induction i using Fin.addCases with
    | left i => simp [Circuit.fixedInputWires]
    | right i =>
      cases hy : y i <;>
        simp [Circuit.fixedInputWires, hy, Program.boolConstants, Program.trace, Program.eval,
          Line.eval, Interpretation.withBoolConstants, Wire.elim] <;> rfl
  funext o
  change (Program.boolConstants σ n |>.append (Circuit.fixedInputWires y)
    c.program.withBoolConstants).trace I.withBoolConstants x
      (Program.appendedWire (Circuit.fixedInputWires y) (c.outputs o)) = _
  rw [Program.trace_append_appendedWire, hfeed, Program.trace_withBoolConstants]
  rfl

end Cslib.Circuits
