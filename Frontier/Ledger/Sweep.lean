/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Ledger.Basic
public import Frontier.Compiler
import Mathlib.Tactic.Ring

/-!
# Sweeping a circuit with a ledger

Let a circuit with one output decide a set `S`, and let its special gates have a ledger in `M`.
Erase the special gates, and make every wire an output of the erased program, accepting every
value there, so that every wire is a signal of its network. For a guess `m ∈ M` the network of
the erased program runs the circuit with the placeholders reading their values from `m`; the
graph of the network does not depend on `m`.

**The sweep** (`Frontier.Ledger.sweep`). Lay out the vertices of the network. At time `t` the
inputs read by the first `t` vertices are revealed, and the message of an input `x` of `S` has
three parts: the product `m` of the contributions of the run of `x` (its consistent guess), the
product of the contributions of the wires whose vertices come first (the ledger so far), and the
values of the run on the frontier. Two inputs with the same message can be spliced: the network
of the erased program with guess `m` splices them (the separator lemma), the two parts of the
ledger multiply back to `m`, and a consistent guess yields the true run
(`Frontier.Ledger.mem_of_splice`).

**Transitions.** A transition is determined by the three parts of the messages before and after
the step, the values on the two frontiers, and the inputs read at the vertex processed
(`Frontier.Ledger.ncard_transition_le_width`). If the frontiers lie inside a closed set of
vertices `W`, the values on them are determined by the guess and the inputs read in `W`
(`Frontier.Ledger.run_eq_of_eqOn_readIn`), so the transition is also determined by the guess,
the two ledgers, and the inputs read in `W` (`Frontier.Ledger.ncard_transition_le_closed`). The
second bound is what makes a disconnected network harmless: a component that reads few inputs
has few transitions, however wide its layout.
-/

@[expose] public section

namespace Frontier

namespace Ledger

open Cslib.Circuits Set

universe v

variable {U : Type*} {σ : Signature.{v}} {n : ℕ} {c : Circuit σ n 1} {I : Interpretation σ U}
  {special : ℕ → Prop} {M : Type*} [CommMonoid M] (L : Ledger c.program I special M)

/-! ### The network of the erased program -/

/-- The outputs of the erased program: the output of the circuit, and every wire. -/
def outs (c : Circuit σ n 1) : Option (Wire n c.size) → Wire n c.size
  | none => c.outputs 0
  | some w => w

/-- The accepted values at the outputs of the erased program. -/
def accs (Acc : Set U) {s : ℕ} : Option (Wire n s) → Set U
  | none => Acc
  | some _ => univ

/-- The vertices of the network of the erased program. -/
abbrev Vtx (c : Circuit σ n 1) (special : ℕ → Prop) :=
  Compiler.Vertex (erase special c.program) (outs c)

/-- The edges of the network of the erased program. -/
abbrev Edg (c : Circuit σ n 1) (special : ℕ → Prop) :=
  Compiler.Edge (erase special c.program) (outs c)

/-- The network of the erased program with the guess `m`, accepting the values in `Acc` at the
output of the circuit. -/
noncomputable abbrev net (Acc : Set U) (m : M) :=
  Compiler.network (erase special c.program) (outs c) (guessInterpretation I (L.readout m))
    (accs Acc)

/-- The network of the erased program with the guess `m`, accepting every value. -/
noncomputable abbrev fnet (m : M) :=
  Compiler.network (erase special c.program) (outs c) (guessInterpretation I (L.readout m))
    fun _ => univ

/-- Every wire is a signal. -/
theorem reach (w : Wire n c.size) : Compiler.Reach (erase special c.program) (outs c) w :=
  .out (some w)

/-- The vertex of a wire. -/
def vtx (w : Wire n c.size) : Vtx c special :=
  .signal ⟨w, reach w⟩

open Classical in
/-- The ledger of the wires whose vertices lie in `P`. -/
noncomputable def partialProd (P : Set (Vtx c special)) (v : Wire n c.size → U) : M :=
  ∏ w ∈ Finset.univ.filter (fun w => vtx w ∈ P), L.contribution w (v w)

open Classical in
theorem total_eq_mul (P : Set (Vtx c special)) (v : Wire n c.size → U) :
    L.total v = L.partialProd P v * L.partialProd Pᶜ v := by
  rw [total, partialProd, partialProd, ← Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun w => vtx w ∈ P)]
  simp

/-! ### Splicing -/

/-- The true run satisfies the network of its consistent guess. -/
theorem satisfies_net {Acc : Set U} {x : Fin n → U}
    (hx : c.program.trace I x (c.outputs 0) ∈ Acc) :
    (L.net Acc (L.total (c.program.trace I x))).Satisfies x
      fun e => c.program.trace I x e.signal.1 := by
  have h := Compiler.trace_satisfies (p := erase special c.program) (out := outs c) (x := x)
    (guessInterpretation I (L.readout (L.total (c.program.trace I x)))) (accs Acc) fun o => by
      rcases o with _ | w
      · change L.run _ x (c.outputs 0) ∈ Acc
        rwa [L.run_total_trace]
      · trivial
  convert h using 2 with e
  change _ = L.run _ x _
  rw [L.run_total_trace]

/-- **Splicing two inputs with the same message.** If the runs of two inputs of `S` have the
same consistent guess, the same ledger on `P`, and the same values on the cut of `P`, then the
input that reads like the first at `P` and like the second elsewhere lies in `S`. -/
theorem mem_of_splice {Acc : Set U} {P : Set (Vtx c special)} {x y z : Fin n → U}
    (hx : c.program.trace I x (c.outputs 0) ∈ Acc) (hy : c.program.trace I y (c.outputs 0) ∈ Acc)
    (hm : L.total (c.program.trace I x) = L.total (c.program.trace I y))
    (hpart : L.partialProd P (c.program.trace I x) = L.partialProd P (c.program.trace I y))
    (hcut : ∀ e ∈ (L.net Acc (L.total (c.program.trace I y))).cut P,
      c.program.trace I x e.signal.1 = c.program.trace I y e.signal.1)
    (hzx : EqOn z x ((L.net Acc (L.total (c.program.trace I y))).readIn P))
    (hzy : EqOn z y ((L.net Acc (L.total (c.program.trace I y))).readIn P)ᶜ) :
    c.program.trace I z (c.outputs 0) ∈ Acc := by
  classical
  generalize hmdef : L.total (c.program.trace I y) = m at hcut hzx hzy
  have hαx := L.satisfies_net hx
  have hαy := L.satisfies_net hy
  rw [hm, hmdef] at hαx
  rw [hmdef] at hαy
  obtain ⟨γ, hγ, hγx, hγy⟩ := hαx.splice hαy hcut hzx hzy
  -- The spliced assignment is the run of `z` with the guess `m`.
  have hγrun : ∀ e, γ e = L.run m z e.signal.1 := fun e => Compiler.eq_trace hγ e
  -- On each wire, the run of `z` agrees with `x` at `P` and with `y` elsewhere.
  have hwire : ∀ w, L.run m z w =
      if vtx w ∈ P then c.program.trace I x w else c.program.trace I y w := by
    intro w
    have hhead : (Compiler.head ⟨w, reach w⟩ : Edg c special).signal.1 = w := rfl
    rw [← hhead, ← hγrun]
    split_ifs with hw
    · exact hγx (Or.inl hw)
    · by_cases ht : Compiler.head ⟨w, reach w⟩ ∈ (L.net Acc m).touching P
      · rw [hγx ht]
        refine hcut _ ?_
        rcases ht with ht | ht
        · exact absurd ht hw
        · simp only [Multigraph.mem_cut]
          exact fun h => hw (h.mpr ht)
      · exact hγy ht
  -- The ledger of the run of `z` is `m`, so the guess is consistent.
  have htotal : L.total (L.run m z) = m := by
    rw [L.total_eq_mul P]
    conv_rhs => rw [← hmdef, L.total_eq_mul P (c.program.trace I y)]
    congr 1
    · rw [← hpart]
      refine Finset.prod_congr rfl fun w hw => ?_
      have hw' : vtx w ∈ P := by simpa using hw
      rw [hwire]
      simp [hw']
    · refine Finset.prod_congr rfl fun w hw => ?_
      have hw' : vtx w ∉ P := by simpa using hw
      rw [hwire]
      simp [hw']
  have hrun := L.run_eq_trace htotal
  -- The output check of the spliced assignment.
  have hout : γ (Compiler.outEdge none) ∈ Acc := hγ (.output none)
  rw [hγrun, Compiler.signal_outEdge, hrun] at hout
  exact hout

/-- **Locality inside a closed set.** For a fixed guess, the values of the run on the edges at a
closed set of vertices `W` depend only on the inputs read in `W`. -/
theorem run_eq_of_eqOn_readIn (m : M) {W : Set (Vtx c special)}
    (hW : (L.fnet m).cut W = ∅) {x x' : Fin n → U} (hxx' : EqOn x x' ((L.fnet m).readIn W))
    {e : Edg c special} (he : e ∈ (L.fnet m).touching W) :
    L.run m x e.signal.1 = L.run m x' e.signal.1 := by
  have hα := Compiler.trace_satisfies (p := erase special c.program) (out := outs c) (x := x)
    (guessInterpretation I (L.readout m)) (fun _ => univ) fun _ => trivial
  have hα' := Compiler.trace_satisfies (p := erase special c.program) (out := outs c) (x := x')
    (guessInterpretation I (L.readout m)) (fun _ => univ) fun _ => trivial
  obtain ⟨γ, hγ, hγx, -⟩ := hα.splice hα' (by rw [hW]; exact eqOn_empty _ _) hxx'.symm
    (eqOn_refl _ _)
  change (erase special c.program).trace _ x _ = (erase special c.program).trace _ x' _
  rw [← Compiler.eq_trace hγ e]
  exact (hγx he).symm

/-! ### The sweep -/

section Sweep

variable (Acc : Set U)

/-- Every input is read, at its own vertex. -/
theorem readIn_univ : (L.fnet (1 : M)).readIn univ = univ :=
  eq_univ_of_forall fun i => ⟨_, mem_univ _, Compiler.site_of_reach (reach (.input i))⟩

open Classical in
/-- The message of an input at time `t`: its consistent guess, its ledger on the first `t`
vertices, and its values on the frontier. After the last vertex the message is empty. -/
noncomputable def message (π : Layout (Vtx c special)) (t : ℕ) (x : Fin n → U) :
    M × M × (Edg c special → Option U) :=
  if t < Nat.card (Vtx c special) then
    (L.total (c.program.trace I x), L.partialProd (π.initial t) (c.program.trace I x),
      fun e => if e ∈ (L.fnet 1).cut (π.initial t) then some (c.program.trace I x e.signal.1)
        else none)
  else (1, 1, fun _ => none)

/-- **The sweep of a circuit with a ledger**, along a layout of the network of its erased
program. -/
noncomputable def sweep (π : Layout (Vtx c special)) :
    Sweep {x | c.program.trace I x (c.outputs 0) ∈ Acc} (M × M × (Edg c special → Option U)) where
  length := Nat.card (Vtx c special)
  revealed t := (L.fnet 1).readIn (π.initial t)
  revealed_zero := by simp
  revealed_length := by rw [π.initial_of_card_le le_rfl, L.readIn_univ]
  message := L.message π
  message_length _ _ _ _ := by simp [message]
  splice t x hx y hy hxy z hzx hzy := by
    by_cases ht : t < Nat.card (Vtx c special)
    · simp only [message, ht, ite_true, Prod.mk.injEq] at hxy
      obtain ⟨hm, hpart, hcut⟩ := hxy
      refine L.mem_of_splice hx hy hm hpart (fun e he => ?_) hzx hzy
      have := congrFun hcut e
      simp only [show e ∈ (L.fnet 1).cut (π.initial t) from he, ite_true,
        Option.some.injEq] at this
      exact this
    · rw [π.initial_of_card_le (by omega), L.readIn_univ] at hzx
      rwa [show z = x from funext fun i => hzx (mem_univ i)]

variable {Acc}

/-- The inputs revealed while processing the vertex numbered `t` are read at that vertex. -/
theorem newly_subset_readAt (π : Layout (Vtx c special)) {t : ℕ}
    (ht : t < Nat.card (Vtx c special)) :
    (L.sweep Acc π).newly t ⊆ (L.fnet 1).readAt (π.symm ⟨t, ht⟩) := by
  rintro i ⟨⟨u, hu, hiu⟩, hi'⟩
  change u ∈ π.initial (t + 1) at hu
  rw [π.initial_succ ht] at hu
  rcases hu with rfl | hu
  · exact hiu
  · exact absurd ⟨u, hu, hiu⟩ hi'

/-- **Transitions by width.** A transition is determined by the guess, the two ledgers, the
values on the two frontiers, and the inputs read at the vertex processed. -/
theorem ncard_transition_le_width [Finite U] [Finite M] (π : Layout (Vtx c special)) {t : ℕ}
    (ht : t < Nat.card (Vtx c special)) :
    ((L.sweep Acc π).transition t '' {x | c.program.trace I x (c.outputs 0) ∈ Acc}).ncard ≤
      Nat.card M ^ 3 * Nat.card U ^ (((L.fnet 1).cut (π.initial t) ∪
        (L.fnet 1).cut (π.initial (t + 1))).ncard +
          ((L.fnet 1).readAt (π.symm ⟨t, ht⟩)).ncard) := by
  classical
  set C := (L.fnet 1).cut (π.initial t) ∪ (L.fnet 1).cut (π.initial (t + 1))
  set R := (L.fnet 1).readAt (π.symm ⟨t, ht⟩)
  calc ((L.sweep Acc π).transition t '' _).ncard
      ≤ ((fun x => (L.total (c.program.trace I x),
          L.partialProd (π.initial t) (c.program.trace I x),
          L.partialProd (π.initial (t + 1)) (c.program.trace I x),
          C.domRestrict fun e => c.program.trace I x e.signal.1, R.domRestrict x)) ''
            {x | c.program.trace I x (c.outputs 0) ∈ Acc}).ncard := by
        refine ncard_image_le_ncard_image_of_determines (toFinite _) _ _
          fun x _ y _ hxy => ?_
        simp only [Prod.mk.injEq, domRestrict_eq_domRestrict_iff] at hxy
        obtain ⟨hm, h₀, h₁, hC, hR⟩ := hxy
        have hcut : ∀ t', t' = t ∨ t' = t + 1 → L.message π t' x = L.message π t' y := by
          rintro t' ht'
          unfold message
          by_cases h : t' < Nat.card (Vtx c special)
          · simp only [h, ite_true]
            refine Prod.ext hm (Prod.ext ?_ (funext fun e => ?_))
            · rcases ht' with rfl | rfl
              · exact h₀
              · exact h₁
            · by_cases he : e ∈ (L.fnet 1).cut (π.initial t')
              · have heC : e ∈ C := by
                  rcases ht' with rfl | rfl
                  · exact Or.inl he
                  · exact Or.inr he
                simp only [he, ite_true, hC heC]
              · simp only [he, ite_false]
          · simp only [h, ite_false]
        simp only [Sweep.transition, Prod.mk.injEq, domRestrict_eq_domRestrict_iff]
        exact ⟨hcut t (Or.inl rfl), hcut (t + 1) (Or.inr rfl),
          hR.mono (L.newly_subset_readAt π ht)⟩
    _ ≤ Nat.card (M × M × M × (C → U) × (R → U)) := ncard_le_card _
    _ = Nat.card M ^ 3 * Nat.card U ^ (C.ncard + R.ncard) := by
        simp only [Nat.card_prod, Nat.card_fun, Nat.card_coe_set_eq, pow_add]
        ring

/-- **Transitions inside a closed set.** If the vertex processed lies in a closed set `W` that
contains both frontiers, a transition is determined by the guess, the two ledgers, and the
inputs read in `W`. -/
theorem ncard_transition_le_closed [Finite U] [Finite M] (π : Layout (Vtx c special)) {t : ℕ}
    (ht : t < Nat.card (Vtx c special)) {W : Set (Vtx c special)}
    (hW : (L.fnet 1).cut W = ∅) (hv : π.symm ⟨t, ht⟩ ∈ W)
    (hC : (L.fnet 1).cut (π.initial t) ∪ (L.fnet 1).cut (π.initial (t + 1)) ⊆
      (L.fnet 1).touching W) :
    ((L.sweep Acc π).transition t '' {x | c.program.trace I x (c.outputs 0) ∈ Acc}).ncard ≤
      Nat.card M ^ 3 * Nat.card U ^ ((L.fnet 1).readIn W).ncard := by
  classical
  set R := (L.fnet 1).readIn W
  calc ((L.sweep Acc π).transition t '' _).ncard
      ≤ ((fun x => (L.total (c.program.trace I x),
          L.partialProd (π.initial t) (c.program.trace I x),
          L.partialProd (π.initial (t + 1)) (c.program.trace I x), R.domRestrict x)) ''
            {x | c.program.trace I x (c.outputs 0) ∈ Acc}).ncard := by
        refine ncard_image_le_ncard_image_of_determines (toFinite _) _ _
          fun x _ y _ hxy => ?_
        simp only [Prod.mk.injEq, domRestrict_eq_domRestrict_iff] at hxy
        obtain ⟨hm, h₀, h₁, hR⟩ := hxy
        -- On the edges at `W`, the runs of `x` and `y` agree.
        have hW' : ∀ e ∈ (L.fnet 1).touching W,
            c.program.trace I x e.signal.1 = c.program.trace I y e.signal.1 := by
          intro e he
          rw [← L.run_total_trace x, ← L.run_total_trace y, ← hm]
          exact L.run_eq_of_eqOn_readIn (L.total (c.program.trace I x)) hW hR he
        have hcut : ∀ t', t' = t ∨ t' = t + 1 → L.message π t' x = L.message π t' y := by
          rintro t' ht'
          unfold message
          by_cases h : t' < Nat.card (Vtx c special)
          · simp only [h, ite_true]
            refine Prod.ext hm (Prod.ext ?_ (funext fun e => ?_))
            · rcases ht' with rfl | rfl
              · exact h₀
              · exact h₁
            · by_cases he : e ∈ (L.fnet 1).cut (π.initial t')
              · have heC : e ∈ (L.fnet 1).touching W := by
                  rcases ht' with rfl | rfl
                  · exact hC (Or.inl he)
                  · exact hC (Or.inr he)
                simp only [he, ite_true, hW' e heC]
              · simp only [he, ite_false]
          · simp only [h, ite_false]
        simp only [Sweep.transition, Prod.mk.injEq, domRestrict_eq_domRestrict_iff]
        refine ⟨hcut t (Or.inl rfl), hcut (t + 1) (Or.inr rfl), fun i hi => hR ?_⟩
        exact ⟨_, hv, L.newly_subset_readAt π ht hi⟩
    _ ≤ Nat.card (M × M × M × (R → U)) := ncard_le_card _
    _ = Nat.card M ^ 3 * Nat.card U ^ R.ncard := by
        simp only [Nat.card_prod, Nat.card_fun, Nat.card_coe_set_eq]
        ring

end Sweep

end Ledger

end Frontier
