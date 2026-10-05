/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Frontier.Multigraph
public import Frontier.Sweep

/-!
# Constraint networks and their sweeps

A *constraint network* is a multigraph whose edges carry values in an alphabet `U` and whose
vertices impose *local constraints*: the constraint at `v` sees only the values on the edges at
`v` and the inputs read at `v`. Each input is read at no more than one vertex. An input is
*accepted* when some assignment of values to the edges satisfies every constraint.

Networks are a semantics-free form of computation. Nothing in them is directed: a gate
`z = g(x, y)` becomes the relation `{(x, y, z) | z = g(x, y)}` between three edge values, and
the network never needs to invert `g`.

**The separator lemma** (`Network.Satisfies.splice`). Cut the vertices into a set `L` and its
complement. If two satisfying assignments, for inputs `x` and `y`, agree on the cut, then
taking the first assignment near `L` and the second away from it satisfies the network for the
input that reads like `x` at `L` and like `y` elsewhere. Once the values on the cut are fixed,
the two sides of the network are independent.

**Sweeping a network.** Process the vertices in the order of a layout. At time `t` the inputs
read by the first `t` vertices are revealed, and the message is the list of values on the
*frontier*, the cut after the first `t` vertices (`Network.sweep`). By the separator lemma
this is a sweep of the accepted set. A transition is determined by the values on two
consecutive frontiers and the inputs read at the vertex processed in between, so a layout of
width `w` in a network of degree at most `d`, reading at most `m` inputs per vertex, yields at
most `|U| ^ (w + d + m)` transitions per step (`Network.ncard_accepted_le`). One last step
reveals the inputs that the network does not read.

## Main definitions

* `Frontier.Network U ι V E`: a constraint network.
* `Frontier.Network.accepted`: its accepted inputs.
* `Frontier.Network.sweep`: the sweep of the accepted set along a layout.

## Main results

* `Frontier.Network.Satisfies.splice`: the separator lemma.
* `Frontier.Network.dependsOn_read`: acceptance depends only on the inputs read.
* `Frontier.Network.ncard_accepted_le`: the frontier counting lemma for networks.
-/

@[expose] public section

namespace Frontier

open Set

/-- A *constraint network* over the alphabet `U` with inputs indexed by `ι`: a multigraph on
vertices `V` and edges `E`, the vertex at which each input is read (if any), and a constraint at
each vertex that sees only the edges at that vertex and the inputs read there. -/
structure Network (U ι V E : Type*) extends Multigraph V E where
  /-- The vertex at which each input is read, if it is read at all. -/
  site : ι → Option V
  /-- The constraint at a vertex, on the input and the values on the edges. -/
  Check : V → (ι → U) → (E → U) → Prop
  /-- Constraints are local: the constraint at `v` sees only the inputs read at `v` and the
  values on the edges incident to `v`. -/
  check_local : ∀ v x x' α α', (∀ i, site i = some v → x i = x' i) →
    (∀ e, src e = v ∨ tgt e = v → α e = α' e) → Check v x α → Check v x' α'

namespace Network

variable {U ι V E : Type*} (N : Network U ι V E)

/-- An assignment of values to the edges satisfies every constraint on the input `x`. -/
def Satisfies (x : ι → U) (α : E → U) : Prop :=
  ∀ v, N.Check v x α

/-- The *accepted* inputs: those with a satisfying assignment. -/
def accepted : Set (ι → U) :=
  {x | ∃ α, N.Satisfies x α}

/-- The inputs read at a vertex. -/
def readAt (v : V) : Set ι :=
  {i | N.site i = some v}

/-- The inputs read at the vertices of `L`. -/
def readIn (L : Set V) : Set ι :=
  {i | ∃ v ∈ L, N.site i = some v}

/-- The inputs read by the network. -/
def read : Set ι :=
  N.readIn univ

/-- The edges with an endpoint in `L`. -/
def touching (L : Set V) : Set E :=
  {e | N.src e ∈ L ∨ N.tgt e ∈ L}

@[simp] theorem readIn_empty : N.readIn ∅ = ∅ := by
  ext i; simp [readIn]

/-- **The separator lemma.** Let `α` satisfy the network on the input `x` and `β` on the input
`y`, and suppose that they agree on the cut of `L`. Then the network is satisfied on any input
`z` that agrees with `x` on the inputs read in `L` and with `y` on the others, by an assignment
that agrees with `α` on the edges touching `L` and with `β` on the remaining edges. -/
theorem Satisfies.splice {N : Network U ι V E} {L : Set V} {x y z : ι → U} {α β : E → U}
    (hx : N.Satisfies x α) (hy : N.Satisfies y β) (hcut : EqOn α β (N.cut L))
    (hzx : EqOn z x (N.readIn L)) (hzy : EqOn z y (N.readIn L)ᶜ) :
    ∃ γ, N.Satisfies z γ ∧ EqOn γ α (N.touching L) ∧ EqOn γ β (N.touching L)ᶜ := by
  classical
  refine ⟨(N.touching L).piecewise α β, fun v => ?_,
    fun e he => piecewise_eq_of_mem _ _ _ he, fun e he => piecewise_eq_of_notMem _ _ _ he⟩
  by_cases hv : v ∈ L
  · -- Near `L`, the spliced assignment is `α` and the input reads like `x`.
    refine N.check_local v x z α _ (fun i hi => (hzx ⟨v, hv, hi⟩).symm) (fun e he => ?_) (hx v)
    have : e ∈ N.touching L := by rcases he with h | h <;> [left; right] <;> rw [h] <;> exact hv
    exact (piecewise_eq_of_mem _ _ _ this).symm
  · -- Away from `L`, it is `β` and the input reads like `y`; the two agree on the cut.
    have hinputs : ∀ i, N.site i = some v → y i = z i := by
      intro i hi
      refine (hzy fun hiL => ?_).symm
      obtain ⟨u, hu, hiu⟩ := hiL
      exact hv (Option.some_injective _ (hiu.symm.trans hi) ▸ hu)
    have hedges : ∀ e, N.src e = v ∨ N.tgt e = v → β e = (N.touching L).piecewise α β e := by
      intro e he
      by_cases ht : e ∈ N.touching L
      · rw [piecewise_eq_of_mem _ _ _ ht]
        refine (hcut ?_).symm
        rcases he with h | h <;> rcases ht with h' | h' <;> simp_all [Multigraph.mem_cut]
      · exact (piecewise_eq_of_notMem _ _ _ ht).symm
    exact N.check_local v y z β _ hinputs hedges (hy v)

/-- Acceptance depends only on the inputs that the network reads. -/
theorem dependsOn_read : DependsOn (· ∈ N.accepted) N.read := by
  have key : ∀ x y : ι → U, (∀ i ∈ N.read, x i = y i) → x ∈ N.accepted → y ∈ N.accepted :=
    fun x y hxy ⟨α, hα⟩ => ⟨α, fun v =>
      N.check_local v x y α α (fun i hi => hxy i ⟨v, mem_univ v, hi⟩) (fun _ _ => rfl) (hα v)⟩
  exact fun x y hxy => propext ⟨key x y hxy, key y x fun i hi => (hxy i hi).symm⟩

/-! ### Sweeping a network along a layout -/

section Sweep

variable [Nonempty U] (π : Layout V)

/-- The *frontier* at time `t`: the cut after the first `t` vertices of the layout. -/
def frontier (t : ℕ) : Set E :=
  N.cut (π.initial t)

/-- A satisfying assignment for an accepted input, chosen once and for all. -/
noncomputable def witness (x : ι → U) : E → U :=
  Classical.epsilon (N.Satisfies x)

theorem satisfies_witness {x : ι → U} (hx : x ∈ N.accepted) : N.Satisfies x (N.witness x) :=
  Classical.epsilon_spec hx

open Classical in
/-- The message at time `t`: the values of the witness on the frontier. -/
noncomputable def message (t : ℕ) (x : ι → U) : E → Option U := fun e =>
  if e ∈ N.frontier π t then some (N.witness x e) else none

open Classical in
/-- The inputs revealed by time `t`: those read by the first `t` vertices, and after the last
vertex, all inputs, including those the network does not read. -/
def revealedBy (t : ℕ) : Set ι :=
  if t ≤ Nat.card V then N.readIn (π.initial t) else univ

theorem message_eq_message_iff {t : ℕ} {x y : ι → U} :
    N.message π t x = N.message π t y ↔ EqOn (N.witness x) (N.witness y) (N.frontier π t) := by
  constructor
  · intro h e he
    simpa [message, he] using congrFun h e
  · intro h
    funext e
    by_cases he : e ∈ N.frontier π t
    · simp [message, he, h he]
    · simp [message, he]

/-- **Sweeping a network along a layout.** The frontier messages form a sweep of the accepted
inputs; the sufficiency of the messages is the separator lemma. -/
noncomputable def sweep [Finite V] : Sweep N.accepted (E → Option U) where
  length := Nat.card V + 1
  revealed := N.revealedBy π
  revealed_zero := by simp [revealedBy]
  revealed_length := by simp [revealedBy]
  message := N.message π
  message_length x _ y _ := by
    rw [message_eq_message_iff, frontier, π.initial_of_card_le (by omega), Multigraph.cut_univ]
    exact eqOn_empty _ _
  splice t x hx y hy hxy z hzx hzy := by
    unfold revealedBy at hzx hzy
    split_ifs at hzx hzy with ht
    · exact ((N.satisfies_witness hx).splice (N.satisfies_witness hy)
        ((N.message_eq_message_iff π).mp hxy) hzx hzy).imp fun _ h => h.1
    · rwa [show z = x from funext fun i => hzx (mem_univ i)]

variable [Finite V]

/-- The inputs revealed while processing the vertex numbered `t` are read at that vertex. -/
theorem newly_subset_readAt {t : ℕ} (ht : t < Nat.card V) :
    (N.sweep π).newly t ⊆ N.readAt (π.symm ⟨t, ht⟩) := by
  rintro i ⟨hi, hi'⟩
  simp only [sweep, revealedBy, show t + 1 ≤ Nat.card V by omega, ht.le, ite_true] at hi hi'
  obtain ⟨u, hu, hiu⟩ := hi
  have hut : (π u : ℕ) = t := by
    by_contra hne
    exact hi' ⟨u, show (π u : ℕ) < t by have := (π.mem_initial).mp hu; omega, hiu⟩
  simp only [readAt, mem_ofPred_eq, hiu, Option.some.injEq]
  exact π.symm_apply_eq.mpr (Fin.ext hut.symm) |>.symm

/-- At a step that processes a vertex, the transition is determined by the values on the two
frontiers and the inputs read at the vertex. -/
theorem ncard_transition_le [Finite ι] [Finite U] [Finite E] {t : ℕ} (ht : t < Nat.card V) :
    ((N.sweep π).transition t '' N.accepted).ncard ≤
      Nat.card U ^ ((N.frontier π t ∪ N.frontier π (t + 1)).ncard +
        (N.readAt (π.symm ⟨t, ht⟩)).ncard) := by
  set C := N.frontier π t ∪ N.frontier π (t + 1)
  set R := N.readAt (π.symm ⟨t, ht⟩)
  calc ((N.sweep π).transition t '' N.accepted).ncard
      ≤ ((fun x => (C.domRestrict (N.witness x), R.domRestrict x)) '' N.accepted).ncard := by
        refine ncard_image_le_ncard_image_of_determines (toFinite _) _ _
          fun x _ y _ hxy => ?_
        simp only [Prod.mk.injEq, domRestrict_eq_domRestrict_iff] at hxy
        simp only [Sweep.transition, sweep, Prod.mk.injEq, message_eq_message_iff,
          domRestrict_eq_domRestrict_iff]
        exact ⟨hxy.1.mono subset_union_left, hxy.1.mono subset_union_right,
          hxy.2.mono (N.newly_subset_readAt π ht)⟩
    _ ≤ Nat.card ((C → U) × (R → U)) := ncard_le_card _
    _ = Nat.card U ^ (C.ncard + R.ncard) := by
        rw [Nat.card_prod, Nat.card_fun, Nat.card_fun, Nat.card_coe_set_eq,
          Nat.card_coe_set_eq, pow_add]

/-- At the last step nothing is left on the frontier, and the transition is determined by the
inputs that the network does not read. -/
theorem ncard_transition_last_le [Finite ι] [Finite U] :
    ((N.sweep π).transition (Nat.card V) '' N.accepted).ncard ≤ Nat.card U ^ N.readᶜ.ncard := by
  have hnewly : (N.sweep π).newly (Nat.card V) = N.readᶜ := by
    simp [Sweep.newly, sweep, revealedBy, read, π.initial_of_card_le le_rfl, compl_eq_univ_sdiff]
  calc ((N.sweep π).transition (Nat.card V) '' N.accepted).ncard
      ≤ (N.readᶜ.domRestrict '' N.accepted).ncard := by
        refine ncard_image_le_ncard_image_of_determines (toFinite _) _ _
          fun x _ y _ hxy => ?_
        rw [domRestrict_eq_domRestrict_iff] at hxy
        simp only [Sweep.transition, sweep, Prod.mk.injEq, message_eq_message_iff,
          domRestrict_eq_domRestrict_iff, frontier,
          π.initial_of_card_le le_rfl, π.initial_of_card_le (Nat.le_succ _),
          Multigraph.cut_univ, eqOn_empty, true_and]
        exact hnewly ▸ hxy
    _ ≤ Nat.card (↥N.readᶜ → U) := ncard_le_card _
    _ = Nat.card U ^ N.readᶜ.ncard := by rw [Nat.card_fun, Nat.card_coe_set_eq]

/-- **The frontier counting lemma for networks.** Let the accepted inputs of a network be
`K`-rectangle-free, with at least `K` of them. If a layout has all frontiers of size at most
`w`, every vertex has degree at most `d` and reads at most `m` inputs, then

`|accepted| ≤ (K - 1) ^ 2 · (|V| · |U| ^ (w + d + m) + |U| ^ #(unread inputs))`. -/
theorem ncard_accepted_le [Finite ι] [Finite U] [Finite E] {K : ℕ}
    (hfree : RectangleFree N.accepted K) (hK : K ≤ N.accepted.ncard)
    {w d m : ℕ} (hw : ∀ t, (N.frontier π t).ncard ≤ w) (hd : N.MaxDegreeLE d)
    (hm : ∀ v, (N.readAt v).ncard ≤ m) :
    N.accepted.ncard ≤
      (K - 1) ^ 2 * (Nat.card V * Nat.card U ^ (w + d + m) + Nat.card U ^ N.readᶜ.ncard) := by
  have hq : 1 ≤ Nat.card U := Nat.card_pos
  refine ((N.sweep π).ncard_le hfree hK).trans (Nat.mul_le_mul_left _ ?_)
  rw [show (N.sweep π).length = Nat.card V + 1 from rfl, Finset.sum_range_succ]
  refine add_le_add ?_ (N.ncard_transition_last_le π)
  calc ∑ t ∈ Finset.range (Nat.card V), ((N.sweep π).transition t '' N.accepted).ncard
      ≤ ∑ _t ∈ Finset.range (Nat.card V), Nat.card U ^ (w + d + m) := by
        refine Finset.sum_le_sum fun t ht => ?_
        have ht : t < Nat.card V := Finset.mem_range.mp ht
        refine (N.ncard_transition_le π ht).trans (Nat.pow_le_pow_right hq ?_)
        -- The next frontier differs from this one only at the edges of the vertex processed.
        have hnext : N.frontier π (t + 1) ⊆ N.frontier π t ∪ N.edgesAt (π.symm ⟨t, ht⟩) := by
          rw [frontier, π.initial_succ ht]
          exact N.cut_insert_subset _ _
        have hC : (N.frontier π t ∪ N.frontier π (t + 1)).ncard ≤ w + d :=
          calc (N.frontier π t ∪ N.frontier π (t + 1)).ncard
              ≤ (N.frontier π t ∪ N.edgesAt (π.symm ⟨t, ht⟩)).ncard :=
                ncard_le_ncard (union_subset subset_union_left hnext) (toFinite _)
            _ ≤ (N.frontier π t).ncard + (N.edgesAt (π.symm ⟨t, ht⟩)).ncard := ncard_union_le _ _
            _ ≤ w + d := add_le_add (hw t) (hd _)
        have := hm (π.symm ⟨t, ht⟩)
        omega
    _ = Nat.card V * Nat.card U ^ (w + d + m) := by simp

end Sweep

end Network

end Frontier
