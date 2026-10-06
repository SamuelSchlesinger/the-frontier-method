/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Compiler
public import Frontier.ForMathlib.SetCard

/-!
# Mixed input-output fibers

For an arbitrary map, specify some input coordinates and some output coordinates. The
largest remaining fiber measures ambiguity in this mixed observation. Equal frontier
values permit two complementary splices, embedding each frontier class in the product of
two mixed fibers. No linearity or algebra on the alphabet is needed.

A map `F : U^N → U^N` is *MDS* when any balanced mixed observation determines the input
(`IsMDS`); total regularity of a matrix is the linear special case
(`Frontier.TotallyRegular.isMDS`). Every layout of a compiled circuit passes a balanced cut
(`exists_balanced_terminal_cut`), and for an MDS map the frontier values there determine the
input (`exists_injective_cut_mds`). The graph of such a circuit is connected, since every
output depends on every input, and `exists_graph_of_upstream` packages its shape and size
for the demand-and-supply comparison.
-/

@[expose] public section

namespace Frontier

open Set

variable {ι O U M : Type*}

/-- Inputs indistinguishable from `x` after observing the inputs in `X` and outputs in `Y`. -/
def mixedFiber (F : (ι → U) → (O → U)) (X : Set ι) (Y : Set O) (x : ι → U) :
    Set (ι → U) := {z | EqOn z x X ∧ EqOn (F z) (F x) Y}

/-- Largest nonempty fiber of a mixed input-output observation. Empty fibers do not affect
the maximum; indexing by an input therefore includes every relevant observation. -/
noncomputable def maxMixedFiber [Finite ι] [Finite U]
    (F : (ι → U) → (O → U)) (X : Set ι) (Y : Set O) : ℕ := by
  let := Fintype.ofFinite (ι → U)
  exact Finset.univ.sup fun x => (mixedFiber F X Y x).ncard

theorem ncard_mixedFiber_le [Finite ι] [Finite U]
    (F : (ι → U) → (O → U)) (X : Set ι) (Y : Set O) (x : ι → U) :
    (mixedFiber F X Y x).ncard ≤ maxMixedFiber F X Y := by
  classical
  let := Fintype.ofFinite (ι → U)
  exact Finset.le_sup (f := fun x => (mixedFiber F X Y x).ncard) (Finset.mem_univ x)

/-- A boundary code permits splicing the inputs on `X` while preserving the corresponding
outputs on `Y`. This is an observational property, not a causal evaluation order. -/
def OutputSplicing (F : (ι → U) → (O → U)) (X : Set ι) (Y : Set O)
    (message : (ι → U) → M) : Prop :=
  ∀ x y, message x = message y → ∀ z, EqOn z x X → EqOn z y Xᶜ →
    EqOn (F z) (F x) Y ∧ EqOn (F z) (F y) Yᶜ

namespace OutputSplicing

variable [Finite ι] [Finite U] {F : (ι → U) → (O → U)} {X : Set ι} {Y : Set O}
  {message : (ι → U) → M} (h : OutputSplicing F X Y message)

include h

/-- A message class embeds in the product of two complementary mixed fibers. -/
theorem ncard_class_le (x : ι → U) :
    {y | message y = message x}.ncard ≤
      (mixedFiber F X Y x).ncard * (mixedFiber F Xᶜ Yᶜ x).ncard := by
  classical
  rw [← ncard_prod]
  refine ncard_le_ncard_of_injOn
    (fun y => (X.piecewise x y, X.piecewise y x)) ?_ ?_
  · intro y hy
    have hxy := h x y hy.symm _ (X.piecewise_eqOn x y) (X.piecewise_eqOn_compl x y)
    have hyx := h y x hy _ (X.piecewise_eqOn y x) (X.piecewise_eqOn_compl y x)
    exact ⟨⟨X.piecewise_eqOn x y, hxy.1⟩, ⟨X.piecewise_eqOn_compl y x, hyx.2⟩⟩
  · intro y _ z _ he
    have he := Prod.mk.inj he
    funext i
    by_cases hi : i ∈ X
    · simpa [hi] using congrFun he.2 i
    · simpa [hi] using congrFun he.1 i

/-- **Mixed-fiber demand**, in cardinal form. The number of used messages, multiplied by
the two largest complementary fibers, must cover all inputs. -/
theorem card_le :
    Nat.card U ^ Nat.card ι ≤ (Set.range message).ncard *
      (maxMixedFiber F X Y * maxMixedFiber F Xᶜ Yᶜ) := by
  have hf (m : M) : ((univ : Set (ι → U)) ∩ message ⁻¹' {m}).ncard ≤
      maxMixedFiber F X Y * maxMixedFiber F Xᶜ Yᶜ := by
    rcases ((univ : Set (ι → U)) ∩ message ⁻¹' {m}).eq_empty_or_nonempty with he | ⟨x, hx⟩
    · simp [he]
    · have he : ((univ : Set (ι → U)) ∩ message ⁻¹' {m}) =
          {y | message y = message x} := by
        ext y
        simp only [mem_inter_iff, mem_univ, mem_preimage, mem_singleton_iff, true_and,
          mem_ofPred_eq]
        rw [hx.2]
      rw [he]
      exact (h.ncard_class_le x).trans
        (Nat.mul_le_mul (ncard_mixedFiber_le F X Y x) (ncard_mixedFiber_le F Xᶜ Yᶜ x))
  have H := ncard_le_mul_ncard_image (toFinite (univ : Set (ι → U))) message _ hf
  simpa only [ncard_univ, Nat.card_fun, image_univ, Nat.mul_comm] using H

omit [Finite ι] [Finite U] in
/-- When both mixed observations are injective, the boundary code determines the input. -/
theorem injective (hX : ∀ x y, EqOn x y X → EqOn (F x) (F y) Y → x = y)
    (hY : ∀ x y, EqOn x y Xᶜ → EqOn (F x) (F y) Yᶜ → x = y) :
    Function.Injective message := by
  classical
  intro x y hxy
  let z := X.piecewise x y
  have hz := h x y hxy z (X.piecewise_eqOn x y) (X.piecewise_eqOn_compl x y)
  exact (hX z x (X.piecewise_eqOn x y) hz.1).symm.trans
    (hY z y (X.piecewise_eqOn_compl x y) hz.2)

end OutputSplicing

/-! ### MDS maps -/

variable {N : ℕ}

/-- Any balanced mixed observation determines the input. Equivalently, any `N` coordinates
of the systematic graph code `(x, F x)` determine its codeword. -/
def IsMDS (F : (Fin N → U) → (Fin N → U)) : Prop :=
  ∀ X Y : Set (Fin N), X.ncard + Y.ncard = N →
    ∀ x y, EqOn x y X → EqOn (F x) (F y) Y → x = y

theorem IsMDS.mixedFiber_eq_singleton {F : (Fin N → U) → (Fin N → U)} (hF : IsMDS F)
    {X Y : Set (Fin N)} (hXY : X.ncard + Y.ncard = N) (x : Fin N → U) :
    mixedFiber F X Y x = {x} := by
  ext z
  constructor
  · intro hz; exact hF X Y hXY z x hz.1 hz.2
  · rintro rfl; exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- Coordinatewise alphabet permutations preserve the MDS graph-code property. -/
theorem IsMDS.permute {F : (Fin N → U) → (Fin N → U)} (hF : IsMDS F)
    (before after : Fin N → Equiv.Perm U) :
    IsMDS (fun x i => after i (F (fun j => before j (x j)) i)) := by
  intro X Y hXY x y hX hY
  have H := hF X Y hXY (fun j => before j (x j)) (fun j => before j (y j))
    (fun j hj => congrArg (before j) (hX hj))
    (fun i hi => (after i).injective (hY hi))
  exact funext fun j => (before j).injective (congrFun H j)

/-! ### Balanced cuts of compiled circuits -/

open Cslib.Circuits

/-- **A discrete intermediate value theorem.** A sequence of naturals that starts at `0` and
grows by at most one per step takes every value up to its final one. -/
theorem exists_eq_of_le_succ {a : ℕ → ℕ} (h0 : a 0 = 0) {m : ℕ} :
    ∀ {T : ℕ}, m ≤ a T → (∀ t < T, a (t + 1) ≤ a t + 1) → ∃ t ≤ T, a t = m
  | 0, hT, _ => ⟨0, le_rfl, by omega⟩
  | T + 1, hT, hstep => by
    by_cases h : m ≤ a T
    · obtain ⟨t, ht, hat⟩ := exists_eq_of_le_succ h0 h fun t ht => hstep t (by omega)
      exact ⟨t, by omega, hat⟩
    · exact ⟨T + 1, le_rfl, by have := hstep T (by omega); omega⟩

section Circuit

variable {σ : Signature} {I : Interpretation σ U} {c : Circuit σ N N}
  {F : (Fin N → U) → (Fin N → U)}

/-- The MDS property forces every output to depend on every input. -/
theorem upstream_of_mds [Nontrivial U] (hF : IsMDS F) (hc : c.Computes I F)
    (o i : Fin N) : c.program.Upstream (c.outputs o) (.input i) := by
  classical
  by_contra hnot
  obtain ⟨a, b, hab⟩ := exists_pair_ne U
  let x : Fin N → U := fun _ => a
  let y := Function.update x i b
  have hout : c.program.trace I x (c.outputs o) = c.program.trace I y (c.outputs o) := by
    apply c.program.trace_congr I (w := c.outputs o) _ _ .refl
    intro j hj
    have hji : j ≠ i := fun h => hnot (h ▸ hj)
    simp [y, hji]
  have hXY : ({i}ᶜ : Set (Fin N)).ncard + ({o} : Set (Fin N)).ncard = N := by
    have H := ncard_add_ncard_compl ({i} : Set (Fin N))
    simp only [ncard_singleton, Nat.card_eq_fintype_card, Fintype.card_fin] at H ⊢
    omega
  have heq : x = y := hF {i}ᶜ {o} hXY x y
    (fun j hj => by have hji : j ≠ i := hj; simp [y, hji])
    (by
      intro j hj
      have hj : j = o := hj
      subst j
      exact (congrFun (hc x) o).symm.trans (hout.trans (congrFun (hc y) o)))
  exact hab (by simpa [x, y] using congrFun heq i)

/-- Every layout passes a balanced input-output observation. This statement only needs
the output terminals; some unused inputs are allowed. -/
theorem exists_balanced_terminal_cut (I : Interpretation σ U) (c : Circuit σ N N)
    (π : Layout (Compiler.Vertex c.program c.outputs)) :
    ∃ t, ((Compiler.network c.program c.outputs I fun _ => univ).readIn (π.initial t)).ncard +
      {o | Compiler.Vertex.output o ∈ π.initial t}.ncard = N := by
  classical
  let G := Compiler.network c.program c.outputs I fun _ => univ
  let outs (P : Set (Compiler.Vertex c.program c.outputs)) := {o | Compiler.Vertex.output o ∈ P}
  let a (t : ℕ) := (G.readIn (π.initial t)).ncard + (outs (π.initial t)).ncard
  have h0 : a 0 = 0 := by simp [a, outs, Network.readIn]
  have hT : N ≤ a (Nat.card (Compiler.Vertex c.program c.outputs)) := by
    simp only [a, π.initial_of_card_le le_rfl, outs, mem_univ, ofPred_true, ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hstep : ∀ t < Nat.card (Compiler.Vertex c.program c.outputs), a (t + 1) ≤ a t + 1 := by
    intro t ht
    set v := π.symm ⟨t, ht⟩
    have hsucc := π.initial_succ ht
    have hread : G.readIn (π.initial (t + 1)) ⊆ G.readIn (π.initial t) ∪ G.readAt v := by
      rintro i ⟨u, hu, hiu⟩
      rw [hsucc] at hu
      rcases hu with rfl | hu
      · exact Or.inr hiu
      · exact Or.inl ⟨u, hu, hiu⟩
    have houts : outs (π.initial (t + 1)) ⊆ outs (π.initial t) ∪ {o | .output o = v} := by
      intro o ho
      simp only [outs, mem_ofPred_eq, hsucc, mem_insert_iff] at ho
      exact ho.elim Or.inr Or.inl
    have hv : (G.readAt v).ncard + {o | Compiler.Vertex.output o = v}.ncard ≤ 1 := by
      rcases hvv : v with w | j | o
      · have h1 := Compiler.ncard_readAt_le I (fun _ => univ) (Compiler.Vertex.signal w)
        have h2 : {o | (Compiler.Vertex.output o : Compiler.Vertex c.program c.outputs) =
            Compiler.Vertex.signal w}.ncard = 0 := by simp
        dsimp [G] at *
        omega
      · have h1 : G.readAt (.junction j) = ∅ := by
          ext i
          simp only [Network.readAt, mem_ofPred_eq, mem_empty_iff_false, iff_false]
          intro hi
          obtain ⟨_, h⟩ := Compiler.site_eq_some hi
          cases h
        simp [h1]
      · have h1 : G.readAt (.output o) = ∅ := by
          ext i
          simp only [Network.readAt, mem_ofPred_eq, mem_empty_iff_false, iff_false]
          intro hi
          obtain ⟨_, h⟩ := Compiler.site_eq_some hi
          cases h
        simp [h1]
    have := ncard_le_ncard hread (toFinite _)
    have := ncard_le_ncard houts (toFinite _)
    have := ncard_union_le (G.readIn (π.initial t)) (G.readAt v)
    have := ncard_union_le (outs (π.initial t)) {o | Compiler.Vertex.output o = v}
    dsimp [a]
    omega
  obtain ⟨t, _, ht⟩ := exists_eq_of_le_succ h0 hT hstep
  exact ⟨t, ht⟩

/-- The frontier of a balanced cut determines the input of an MDS map. -/
theorem exists_injective_cut_mds (hF : IsMDS F) (hc : c.Computes I F)
    (π : Layout (Compiler.Vertex c.program c.outputs)) :
    ∃ t, Function.Injective fun (x : Fin N → U)
      (e : ↥((Compiler.network c.program c.outputs I fun _ => univ).cut (π.initial t))) =>
        c.program.trace I x e.1.signal.1 := by
  classical
  obtain ⟨t, ht⟩ := exists_balanced_terminal_cut I c π
  let G := Compiler.network c.program c.outputs I fun _ => univ
  let X := G.readIn (π.initial t)
  let Y := {o | Compiler.Vertex.output o ∈ π.initial t}
  have hXY : X.ncard + Y.ncard = N := ht
  have hcomp : Xᶜ.ncard + Yᶜ.ncard = N := by
    have hX := ncard_add_ncard_compl X
    have hY := ncard_add_ncard_compl Y
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hX hY
    omega
  have hsplice : OutputSplicing F X Y
      (fun (x : Fin N → U) (e : ↥(G.cut (π.initial t))) => c.program.trace I x e.1.signal.1) := by
    intro x y hxy z hzx hzy
    have H := Compiler.trace_out_of_cut I
      (fun e he => congrFun hxy ⟨e, he⟩) hzx hzy
    have htrace (x : Fin N → U) (o : Fin N) := congrFun (hc x) o
    exact ⟨fun o ho => (htrace z o).symm.trans ((H o).1 ho |>.trans (htrace x o)),
      fun o ho => (htrace z o).symm.trans ((H o).2 ho |>.trans (htrace y o))⟩
  exact ⟨t, hsplice.injective (hF X Y hXY) (hF Xᶜ Yᶜ hcomp)⟩

/-- **The graph of a circuit all of whose outputs depend on all of its inputs.** With `s` inner
gates of fan-in at most `r ≥ 2`, the network is a connected, loopless multigraph of maximum
degree `r + 1` with at most `2 r s + 3 N` vertices and cycle rank at most `(r - 1) s + 1 - N`.
The demand on its layouts is whatever the frontier argument supplies. -/
theorem exists_graph_of_upstream (hN : 1 ≤ N) {r : ℕ} (hr : 2 ≤ r) (hfan : c.FanInAtMost r)
    (hup : ∀ o i, c.program.Upstream (c.outputs o) (.input i))
    (hwidth : ∀ π : Layout (Compiler.Vertex c.program c.outputs), ∃ t,
      N ≤ ((Compiler.network c.program c.outputs I fun _ => univ).cut (π.initial t)).ncard) :
    ∃ (V E : Type) (_ : Finite V) (_ : Finite E) (G : Multigraph V E),
      G.Connected ∧ G.Loopless ∧ G.MaxDegreeLE (r + 1) ∧
      Nat.card V ≤ 2 * r * c.innerSize + 3 * N ∧
      G.cycleRank + N ≤ (r - 1) * c.innerSize + 1 ∧
      ∀ π : Layout V, ∃ t, N ≤ (G.cut (π.initial t)).ncard := by
  let G := Compiler.network c.program c.outputs I fun _ => univ
  have hconn : G.Connected :=
    Compiler.connected_of_upstream I _ (w₀ := .input ⟨0, hN⟩) fun o => hup o _
  have hread : G.read.ncard = N := by
    have heq : G.read = univ := by
      rw [Compiler.read_network]
      exact eq_univ_of_forall fun i => Compiler.reach_of_upstream (hup i i)
    rw [heq, ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨_, _, inferInstance, inferInstance, G.toMultigraph, hconn, Compiler.loopless I _,
    Compiler.maxDegreeLE I _ hr hfan, ?_, ?_, hwidth⟩
  · simpa [Circuit.innerSize] using Compiler.card_vertex_le (out := c.outputs) hfan
  · have H := Compiler.cycleRank_add_ncard_read_le I _ hfan hconn
    rw [hread] at H
    exact H

end Circuit

namespace Compiler

open Cslib.Circuits

variable {σ : Signature} {n s : ℕ} [Finite O] {p : Program σ n s} {out : O → Wire n s}
  (I : Interpretation σ U)

/-- The signals on a cut, counted once each regardless of copy multiplicity. -/
def cutSignals (P : Set (Vertex p out)) : Set (Signal p out) :=
  Edge.signal '' (network p out I fun _ => univ).cut P

/-- Distinct signal values on a compiled cut satisfy the mixed-output splicing interface. -/
theorem outputSplicing (P : Set (Vertex p out)) :
    OutputSplicing (fun x o => p.trace I x (out o))
      ((network p out I fun _ => univ).readIn P) {o | Vertex.output o ∈ P}
      (fun (x : Fin n → U) (w : cutSignals I P) => p.trace I x w.1.1) := by
  intro x y hxy z hzx hzy
  have hcut : ∀ e ∈ (network p out I fun _ => univ).cut P,
      p.trace I x e.signal.1 = p.trace I y e.signal.1 :=
    fun e he => congrFun hxy ⟨e.signal, ⟨e, he, rfl⟩⟩
  have H := trace_out_of_cut I hcut hzx hzy
  exact ⟨fun o ho => (H o).1 ho, fun o ho => (H o).2 ho⟩

/-- **Pointwise frontier demand for arbitrary maps.** This bounds every cut by its mixed
input-output ambiguity. Taking logarithms gives the additive demand formulation. -/
theorem pow_le_cutSignals_mul_fibers [Finite U] (P : Set (Vertex p out)) :
    Nat.card U ^ n ≤ Nat.card U ^ (cutSignals I P).ncard *
      (maxMixedFiber (fun x o => p.trace I x (out o))
        ((network p out I fun _ => univ).readIn P) {o | Vertex.output o ∈ P} *
      maxMixedFiber (fun x o => p.trace I x (out o))
        ((network p out I fun _ => univ).readIn P)ᶜ {o | Vertex.output o ∈ P}ᶜ) := by
  have H := (outputSplicing I P).card_le
  rw [Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at H
  refine H.trans (Nat.mul_le_mul_right _ ?_)
  calc (range (fun (x : Fin n → U) (w : cutSignals I P) => p.trace I x w.1.1)).ncard
      ≤ Nat.card (cutSignals I P → U) := ncard_le_card _
    _ = Nat.card U ^ (cutSignals I P).ncard := by rw [Nat.card_fun, Nat.card_coe_set_eq]

end Compiler

end Frontier
