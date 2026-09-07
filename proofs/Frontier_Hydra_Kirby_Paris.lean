/-
/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- A *hydra* is a finite rooted tree: a node together with the (finite) list of the
hydras hanging from it.  Only the multiset of children matters for the game, but a list
representation is used so that the type is a genuine inductive type. -/
inductive Hydra : Type
  | node : List Hydra → Hydra

namespace Hydra

/-- Structural induction principle for hydras: to prove a property of every hydra it
suffices to prove it for `node L` assuming it for every element of `L`. -/
theorem ind_children {motive : Hydra → Prop}
    (H : ∀ L : List Hydra, (∀ c ∈ L, motive c) → motive (node L)) (x : Hydra) : motive x :=
  Hydra.rec (motive_1 := motive) (motive_2 := fun L => ∀ c ∈ L, motive c)
    (fun L ih => H L ih)
    (by simp)
    (fun t ts iht ihts c hc => by
      rcases List.mem_cons.1 hc with rfl | hc
      · exact iht
      · exact ihts c hc)
    x

/-- Auxiliary multiset computation: as a multiset, `a ++ x :: b` is `{x}` plus `a ++ b`. -/
theorem coe_append_cons {α : Type*} (a b : List α) (x : α) :
    ((a ++ x :: b : List α) : Multiset α) = {x} + ((a ++ b : List α) : Multiset α) := by
  rw [Multiset.singleton_add, Multiset.cons_coe]
  exact Multiset.coe_eq_coe.2 List.perm_middle

/-- `Inner x y` : the hydra `y` arises from the hydra `x` by one legal Kirby–Paris move
whose chopped head sits at depth at least `2`, so that the head has a grandparent and
the copies grown by the hydra stay inside `x`.

* `grand`: a head (`node []`) is chopped off the child `c = node (ca ++ node [] :: cb)`
  of the root; the child `c` is then replaced by an arbitrary finite number `k` of
  copies of `c' = node (ca ++ cb)`, i.e. of the tree `c` with that head removed.
  The usual rule "grow `n` new copies at stage `n`" is the special case `k = n`;
  since `k` is arbitrary, termination below holds for every growth rule.
* `deep`: the move takes place inside one of the children. -/
inductive Inner : Hydra → Hydra → Prop
  | grand (k : ℕ) (a b ca cb : List Hydra) :
      Inner (node (a ++ node (ca ++ node [] :: cb) :: b))
            (node (a ++ List.replicate k (node (ca ++ cb)) ++ b))
  | deep (a b : List Hydra) {c c' : Hydra} (h : Inner c c') :
      Inner (node (a ++ c :: b)) (node (a ++ c' :: b))

/-- `Step x y` : the hydra `y` arises from `x` by one legal Kirby–Paris move.
Either a head attached directly to the root is chopped off (there is no regrowth then,
since such a head has no grandparent), or the move is an `Inner` one. -/
inductive Step : Hydra → Hydra → Prop
  | top (a b : List Hydra) : Step (node (a ++ node [] :: b)) (node (a ++ b))
  | inner {x y : Hydra} (h : Inner x y) : Step x y

/-- Sanity check: chopping the head of a two-node branch makes the hydra grow
(here three) new heads at the root. -/
example : Step (node [node [node []]]) (node [node [], node [], node []]) :=
  Step.inner (by simpa using Inner.grand 3 [] [] [] [])

/-- Sanity check: a head attached to the root is chopped off without regrowth. -/
example : Step (node [node [], node [node []]]) (node [node [node []]]) := by
  simpa using Step.top [] [node [node []]]

/-- `Below x y` means that `x` is obtained from `y` by one Kirby–Paris move. -/
def Below (x y : Hydra) : Prop := Step y x

/-- The move relation restricted to accessible sources; it is irreflexive by
construction, which is what lets us feed it to the `CutExpand` machinery. -/
def BelowAcc (x y : Hydra) : Prop := Below x y ∧ Acc Below x

theorem acc_not_self {α : Type*} {r : α → α → Prop} {a : α} (h : Acc r a) : ¬ r a a := by
  induction h with
  | intro x _ ih => exact fun hr => ih x hr hr

instance : Std.Irrefl BelowAcc := ⟨fun _ h => acc_not_self h.2 h.1⟩

theorem belowAcc_sub : Subrelation BelowAcc Below := fun h => h.1

/-- A dead hydra admits no move. -/
theorem step_ne_dead {x y : Hydra} (h : Step x y) : x ≠ node [] := by
  cases h with
  | top a b => simp
  | inner h =>
      cases h with
      | grand k a b ca cb => simp
      | @deep a b c c' h => simp

/-- If a hydra `x` is alive, then a head can be chopped off inside `x`, wherever `x`
sits as a child of some node. -/
theorem exists_inner_of_ne_dead :
    ∀ x : Hydra, x ≠ node [] → ∀ a b : List Hydra, ∃ y, Inner (node (a ++ x :: b)) y := by
  refine ind_children ?_
  intro L ih hL a b
  cases L with
  | nil => exact absurd rfl hL
  | cons c cs =>
      by_cases hc : c = node []
      · subst hc
        exact ⟨_, by simpa using Inner.grand 0 a b [] cs⟩
      · obtain ⟨y, hy⟩ := ih c (by simp) hc [] cs
        exact ⟨_, Inner.deep a b hy⟩

/-- Conversely to `step_ne_dead`: a hydra which is not dead admits a move. -/
theorem exists_step_of_ne_dead (x : Hydra) (hx : x ≠ node []) : ∃ y, Step x y := by
  cases x with
  | node L =>
      cases L with
      | nil => exact absurd rfl hx
      | cons c cs =>
          by_cases hc : c = node []
          · subst hc
            exact ⟨node cs, by simpa using Step.top [] cs⟩
          · obtain ⟨y, hy⟩ := exists_inner_of_ne_dead c hc [] cs
            exact ⟨y, Step.inner (by simpa using hy)⟩

/-- One Kirby–Paris move on `node L` turns the multiset of children `L` into a multiset
obtained by removing one child and adding back finitely many strictly smaller ones:
this is a `CutExpand` step for the move relation. -/
theorem step_cutExpand {L L' : List Hydra} (hacc : ∀ c ∈ L, Acc Below c)
    (h : Step (node L) (node L')) :
    Relation.CutExpand BelowAcc (L' : Multiset Hydra) (L : Multiset Hydra) := by
  cases h with
  | top a b =>
      refine ⟨0, node [], by simp, ?_⟩
      rw [coe_append_cons]
      abel
  | inner h =>
      cases h with
      | grand k a b ca cb =>
          refine ⟨Multiset.replicate k (node (ca ++ cb)), node (ca ++ node [] :: cb), ?_, ?_⟩
          · intro y hy
            rw [Multiset.eq_of_mem_replicate hy]
            exact ⟨Step.top ca cb, Acc.inv (hacc _ (by simp)) (Step.top ca cb)⟩
          · rw [coe_append_cons]
            simp only [← Multiset.coe_add, Multiset.coe_replicate]
            abel
      | @deep a b c c' hcc' =>
          refine ⟨{c'}, c, ?_, ?_⟩
          · intro y hy
            rw [Multiset.mem_singleton.1 hy]
            exact ⟨Step.inner hcc', Acc.inv (hacc _ (by simp)) (Step.inner hcc')⟩
          · rw [coe_append_cons, coe_append_cons]
            abel

/-- Transfer of accessibility from the multiset of children to the hydra itself. -/
theorem acc_of_acc_children {m : Multiset Hydra} (hm : Acc (Relation.CutExpand BelowAcc) m) :
    ∀ L : List Hydra, (L : Multiset Hydra) = m → (∀ c ∈ L, Acc Below c) → Acc Below (node L) := by
  induction hm with
  | intro m _ ih =>
      intro L hLm hL
      refine Acc.intro _ ?_
      rintro x hx
      obtain ⟨L', rfl⟩ : ∃ L', x = node L' := by cases x with | node L' => exact ⟨L', rfl⟩
      have hcut : Relation.CutExpand BelowAcc (L' : Multiset Hydra) (L : Multiset Hydra) :=
        step_cutExpand hL hx
      refine ih (L' : Multiset Hydra) (hLm ▸ hcut) L' rfl ?_
      intro c hc
      have hmem : c ∈ (L' : Multiset Hydra) := by simpa using hc
      have hclosed : ∀ a ∈ (L : Multiset Hydra), Acc Below a := by
        intro a ha; exact hL a (by simpa using ha)
      exact Relation.cutExpand_closed (r := BelowAcc) (fun a => Acc Below a)
        (fun {a' a} hr ha => Acc.inv ha hr.1) hcut hclosed c hmem

/-- **Every hydra is accessible for the Kirby–Paris move relation.** -/
theorem acc_below : ∀ x : Hydra, Acc Below x := by
  refine ind_children ?_
  intro L ih
  have hsing : ∀ c ∈ (L : Multiset Hydra), Acc (Relation.CutExpand BelowAcc) {c} := by
    intro c hc
    exact Acc.cutExpand (belowAcc_sub.accessible (ih c (by simpa using hc)))
  exact acc_of_acc_children (Relation.acc_of_singleton hsing) L rfl (fun c hc => ih c hc)

/-- **Kirby–Paris, well-foundedness form.** The relation "is obtained by one hydra move"
is well founded; equivalently, there is no infinite play. -/
theorem wellFounded_below : WellFounded Below := ⟨acc_below⟩

end Hydra

/-- **The Kirby–Paris hydra theorem.**

Whatever strategy is used — at every stage the player may chop off *any* head, and the
hydra may grow back *any* finite number of copies of the relevant subtree — the game
terminates: the hydra is dead (`Hydra.node []`) after finitely many moves.

Here `H : ℕ → Hydra` is an arbitrary play: as long as the current hydra `H k` is alive,
`H (k+1)` is obtained from it by a legal move (`Hydra.Step`).  The conclusion is that
some `H k` is the dead hydra. -/
theorem Hydra_Kirby_Paris (H : ℕ → Hydra)
    (hplay : ∀ k, H k ≠ Hydra.node [] → Hydra.Step (H k) (H (k + 1))) :
    ∃ k, H k = Hydra.node [] := by
  by_contra hcon
  push_neg at hcon
  have hstep : ∀ k, Hydra.Below (H (k + 1)) (H k) := fun k => hplay k (hcon k)
  -- an infinite descending chain of moves contradicts accessibility of `H 0`
  have key : ∀ x : Hydra, Acc Hydra.Below x → ∀ j : ℕ, H j = x → False := by
    intro x hx
    induction hx with
    | intro y _ ih =>
        intro j hj
        exact ih (H (j + 1)) (hj ▸ hstep j) (j + 1) rfl
  exact key (H 0) (Hydra.acc_below _) 0 rfl

end Frontier

