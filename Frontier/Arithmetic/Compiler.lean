/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Arithmetic.Hessian
public import Frontier.Compiler
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# The mixed-Hessian frontier lemma for polynomial circuits

The compiler's exactness and splicing hold over every alphabet. Applying them over
the two-direction infinitesimal algebra supplies the hypotheses of the algebraic
rank bound, with the actual cut edges as boundary coordinates.
-/

@[expose] public section

namespace Frontier

open Cslib.Circuits Set MvPolynomial

namespace Compiler

variable {σ : Signature} {n s : ℕ} {O U : Type*} [Finite O]
  {p : Program σ n s} {out : O → Wire n s} (I : Interpretation σ U)

/-- Splicing two runs that agree on a cut preserves the cut values themselves. -/
theorem trace_cut_of_cut {P : Set (Vertex p out)} {x y z : Fin n → U}
    (hcut : ∀ e ∈ (network p out I fun _ => univ).cut P,
      p.trace I x e.signal.1 = p.trace I y e.signal.1)
    (hzx : EqOn z x ((network p out I fun _ => univ).readIn P))
    (hzy : EqOn z y ((network p out I fun _ => univ).readIn P)ᶜ)
    {e : Edge p out} (he : e ∈ (network p out I fun _ => univ).cut P) :
    p.trace I z e.signal.1 = p.trace I x e.signal.1 := by
  have hx := trace_satisfies (p := p) (out := out) (x := x) I (fun _ => univ) fun _ => trivial
  have hy := trace_satisfies (p := p) (out := out) (x := y) I (fun _ => univ) fun _ => trivial
  obtain ⟨γ, hγ, hγx, _⟩ := hx.splice hy (fun e he => hcut e he) hzx hzy
  rw [← eq_trace hγ e]
  apply hγx
  by_contra ht
  exact he (iff_of_false (not_or.mp ht).1 (not_or.mp ht).2)

end Compiler

namespace Arithmetic

variable {F : Type*} [Field F] {σ : Signature} {n s : ℕ}
  (P : (o : σ.Op) → MvPolynomial (Fin (σ.Arity o)) F) (p : Program σ n s)

/-- The formal polynomial computed at a wire, obtained by running on indeterminates. -/
noncomputable def wirePolynomial (w : Wire n s) : MvPolynomial (Fin n) F :=
  p.trace (polynomialInterpretation P (MvPolynomial (Fin n) F)) X w

theorem aeval_wirePolynomial {R : Type*} [CommRing R] [Algebra F R]
    (x : Fin n → R) (w : Wire n s) :
    aeval x (wirePolynomial P p w) = p.trace (polynomialInterpretation P R) x w := by
  simpa only [wirePolynomial, aeval_X] using
    map_trace_polynomialInterpretation P (aeval x) p X w

/-- Every variable occurring formally in a wire polynomial is upstream of that wire.
This also covers finite fields and variables with zero formal derivative. -/
theorem upstream_of_mem_vars (i : Fin n) : ∀ (w : Wire n s),
    i ∈ (wirePolynomial P p w).vars → p.Upstream w (.input i)
  | .input j, hi => by
    simp only [wirePolynomial, Program.trace_input, vars_X, Finset.mem_singleton] at hi
    subst j
    exact .refl
  | .gate g, hi => by
    rw [wirePolynomial, p.trace_gate, polynomialInterpretation_apply, aeval_eq_bind₁] at hi
    obtain ⟨a, _, ha⟩ := mem_vars_bind₁ _ _ hi
    exact (Program.Upstream.arg a .refl).trans (upstream_of_mem_vars i _ ha)
termination_by w => match w with | .input _ => 0 | .gate g => g.val + 1
decreasing_by
  generalize hw : (p.lines g).wires a = w at *
  cases w with
  | input => simp
  | gate g' => simpa using p.lines_wires_eq_gate_lt g a hw

variable {O : Type*} [Finite O] (out : O → Wire n s)

/-- Circuit cuts have the infinitesimal splicing property, including preservation of the
boundary itself. The output can lie on either side of the cut. -/
theorem cut_splices (T : Set (Compiler.Vertex p out)) (o : O) :
    Splices (wirePolynomial P p (out o))
      (fun e : ↥((Compiler.network p out (polynomialInterpretation P F) fun _ => univ).cut T) =>
        wirePolynomial P p e.1.signal.1)
      ((Compiler.network p out (polynomialInterpretation P F) fun _ => univ).readIn T) := by
  intro x y z hcut hzx hzy
  have hc : ∀ e ∈ (Compiler.network p out (polynomialInterpretation P (Jet F))
      fun _ => univ).cut T,
      p.trace (polynomialInterpretation P (Jet F)) x e.signal.1 =
        p.trace (polynomialInterpretation P (Jet F)) y e.signal.1 := by
    intro e he
    have h := hcut ⟨e, he⟩
    exact (aeval_wirePolynomial P p x e.signal.1).symm.trans
      (h.trans (aeval_wirePolynomial P p y e.signal.1))
  constructor
  · intro e
    exact (aeval_wirePolynomial P p z e.1.signal.1).trans
      ((Compiler.trace_cut_of_cut _ hc hzx hzy e.property).trans
        (aeval_wirePolynomial P p x e.1.signal.1).symm)
  · have hz := aeval_wirePolynomial P p z (out o)
    have ho := Compiler.trace_out_of_cut _ hc hzx hzy o
    by_cases ht : Compiler.Vertex.output o ∈ T
    · exact Or.inl (hz.trans ((ho.1 ht).trans (aeval_wirePolynomial P p x (out o)).symm))
    · exact Or.inr (hz.trans ((ho.2 ht).trans (aeval_wirePolynomial P p y (out o)).symm))

open Classical in
/-- **Mixed-Hessian frontier lemma.** For every polynomial circuit, every vertex cut,
every scalar output, and every evaluation point, the mixed Hessian rank across the
induced input partition is at most the number of cut edges. -/
theorem rank_mixedHessian_le_cut (T : Set (Compiler.Vertex p out)) (o : O) (a : Fin n → F) :
    (mixedHessian (wirePolynomial P p (out o)) a
      ((Compiler.network p out (polynomialInterpretation P F) fun _ => univ).readIn T)).rank ≤
      ((Compiler.network p out (polynomialInterpretation P F) fun _ => univ).cut T).ncard := by
  let := Fintype.ofFinite ↥((Compiler.network p out (polynomialInterpretation P F)
    fun _ => univ).cut T)
  simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using
    (cut_splices P p out T o).rank_mixedHessian_le a

end Arithmetic
end Frontier
