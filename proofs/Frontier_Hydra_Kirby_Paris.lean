import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- A hydra is a finite rooted tree: a node together with the (finite, ordered) list of the
subtrees hanging from it.  A *head* of the hydra is a leaf, i.e. a subtree `node []`. -/
inductive Hydra : Type
  | node : List Hydra → Hydra

namespace Hydra

/-- Structural induction for `Hydra`: to prove a statement for all hydras it suffices to prove
it for `node ts` assuming it for all subtrees in `ts`. -/
theorem ind {P : Hydra → Prop} (h : ∀ ts : List Hydra, (∀ c ∈ ts, P c) → P (node ts)) :
    ∀ x, P x := by
  have key : ∀ x, P x ∧ True := by
    intro x
    induction x using Hydra.rec (motive_2 := fun l => ∀ c ∈ l, P c) with
    | node ts ih => exact ⟨h ts ih, trivial⟩
    | nil => simp_all
    | cons a l iha ihl =>
        rename_i c hc
        rcases List.mem_cons.1 hc with rfl | hc
        · exact iha.1
        · exact ihl c hc
  exact fun x => (key x).1

end Hydra

open Hydra

/-- Chopping off a head growing directly at the root: a leaf child `node []` of the root is
simply removed (no new heads grow back). -/
inductive Chop : Hydra → Hydra → Prop
  | mk (ts us : List Hydra) : Chop (node (ts ++ us)) (node (ts ++ node [] :: us))

/-- Chopping off a head at depth at least `2`, with the Kirby–Paris regrowth rule with
parameter `n`.

* `grand`: the chopped head is a child of a child `c = node (as ++ node [] :: bs)` of the root.
  The head is removed from `c`, producing `c' = node (as ++ bs)`, and the root (the grandparent
  of the head) then carries `n + 1` copies of `c'` in place of `c`.
* `deeper`: the chopped head lies strictly deeper, so the whole move (removal plus regrowth)
  happens inside one subtree `c` of the root. -/
inductive Deep (n : ℕ) : Hydra → Hydra → Prop
  | grand (ts us as bs : List Hydra) :
      Deep n (node (ts ++ List.replicate (n + 1) (node (as ++ bs)) ++ us))
        (node (ts ++ node (as ++ node [] :: bs) :: us))
  | deeper {c' c : Hydra} (ts us : List Hydra) (hc : Deep n c' c) :
      Deep n (node (ts ++ c' :: us)) (node (ts ++ c :: us))

/-- One move of the Kirby–Paris hydra game with regrowth parameter `n`: `KPStep n H' H` says
that the hydra `H` turns into the hydra `H'` when the player chops off one head and the hydra
grows back `n` extra copies of the relevant branch. -/
def KPStep (n : ℕ) (H' H : Hydra) : Prop := Chop H' H ∨ Deep n H' H

/-- `KPMove H' H` : `H'` arises from `H` by one legal move of the Kirby–Paris hydra game,
for some regrowth parameter. -/
def KPMove (H' H : Hydra) : Prop := ∃ n, KPStep n H' H

/-- The abstract "cut a head, grow smaller branches" relation on hydras: `KPAbs (node ts')
(node ts)` holds when the multiset `ts'` of subtrees is obtained from `ts` by deleting one
subtree `a` and inserting an arbitrary finite multiset of subtrees, each of which is
`KPAbs`-smaller than `a`.  (The equation `ts' + {a} = ts + t` is the `Multiset.erase`-free
formulation used by `Relation.CutExpand`.) -/
inductive KPAbs : Hydra → Hydra → Prop
  | mk (ts ts' t : List Hydra) (a : Hydra) (h : ∀ a' ∈ t, KPAbs a' a)
      (he : (ts' : Multiset Hydra) + {a} = (ts : Multiset Hydra) + (t : Multiset Hydra)) :
      KPAbs (node ts') (node ts)

theorem kpAbs_of_cutExpand {ts ts' : List Hydra}
    (h : Relation.CutExpand KPAbs (ts' : Multiset Hydra) (ts : Multiset Hydra)) :
    KPAbs (node ts') (node ts) := by
  obtain ⟨t, a, hr, he⟩ := h
  refine KPAbs.mk ts ts' t.toList a ?_ ?_
  · intro a' ha'
    exact hr a' (by rwa [← Multiset.mem_coe, Multiset.coe_toList] at ha')
  · rwa [Multiset.coe_toList]

theorem cutExpand_of_kpAbs {ts ts' : List Hydra} (h : KPAbs (node ts') (node ts)) :
    Relation.CutExpand KPAbs (ts' : Multiset Hydra) (ts : Multiset Hydra) := by
  cases h with
  | mk ts₀ ts₀' t a hr he =>
      exact ⟨(t : Multiset Hydra), a, hr, he⟩

theorem KPAbs.irrefl' : ∀ x : Hydra, ¬ KPAbs x x := by
  have key : ∀ x y : Hydra, KPAbs x y → x = y → False := by
    intro x y h
    induction h with
    | mk ts ts' t a hr he ih =>
        intro hEq
        have hts : ts' = ts := by
          cases hEq
          rfl
        subst hts
        have ht : (t : Multiset Hydra) = {a} := by
          have := he
          rw [add_comm ((ts' : Multiset Hydra)) ({a} : Multiset Hydra),
            add_comm ((ts' : Multiset Hydra)) ((t : Multiset Hydra))] at this
          exact (add_right_cancel this).symm
        have hmem : a ∈ t := by
          have : a ∈ (t : Multiset Hydra) := by rw [ht]; simp
          rwa [Multiset.mem_coe] at this
        exact ih a hmem rfl
  intro x hx
  exact key x x hx rfl

instance : Std.Irrefl KPAbs := ⟨KPAbs.irrefl'⟩

theorem acc_node_of_acc_cutExpand {s : Multiset Hydra} (h : Acc (Relation.CutExpand KPAbs) s) :
    ∀ ts : List Hydra, (ts : Multiset Hydra) = s → Acc KPAbs (node ts) := by
  induction h with
  | intro s hs ih =>
      intro ts hts
      refine Acc.intro _ ?_
      rintro y hy
      cases hy with
      | mk ts₀ ts₀' t a hr he =>
          refine ih ((ts₀' : Multiset Hydra)) ?_ ts₀' rfl
          exact hts ▸ (⟨(t : Multiset Hydra), a, hr, he⟩ :
            Relation.CutExpand KPAbs (ts₀' : Multiset Hydra) (ts₀ : Multiset Hydra))

theorem acc_kpAbs (x : Hydra) : Acc KPAbs x := by
  induction x using Hydra.ind with
  | _ ts ih =>
      refine acc_node_of_acc_cutExpand ?_ ts rfl
      refine Relation.acc_of_singleton ?_
      intro a ha
      exact (ih a (by rwa [← Multiset.mem_coe])).cutExpand

theorem wellFounded_kpAbs : WellFounded KPAbs := ⟨acc_kpAbs⟩

theorem kpAbs_of_chop {H' H : Hydra} (h : Chop H' H) : KPAbs H' H := by
  cases h with
  | mk ts us =>
      refine KPAbs.mk (ts ++ node [] :: us) (ts ++ us) [] (node []) (by simp) ?_
      simp [Multiset.coe_add]
      rfl

theorem kpAbs_of_deep {n : ℕ} {H' H : Hydra} (h : Deep n H' H) : KPAbs H' H := by
  induction h with
  | grand ts us as bs =>
      refine KPAbs.mk (ts ++ node (as ++ node [] :: bs) :: us)
        (ts ++ List.replicate (n + 1) (node (as ++ bs)) ++ us)
        (List.replicate (n + 1) (node (as ++ bs))) (node (as ++ node [] :: bs)) ?_ ?_
      · intro a' ha'
        have : a' = node (as ++ bs) := List.eq_of_mem_replicate ha'
        subst this
        exact kpAbs_of_chop (Chop.mk as bs)
      · simp [Multiset.coe_add]
        abel
  | deeper ts us hc ih =>
      rename_i c' c
      refine KPAbs.mk (ts ++ c :: us) (ts ++ c' :: us) [c'] c ?_ ?_
      · intro a' ha'
        have : a' = c' := by simpa using ha'
        subst this
        exact ih
      · simp [Multiset.coe_add]
        abel

theorem kpAbs_of_kpMove {H' H : Hydra} (h : KPMove H' H) : KPAbs H' H := by
  obtain ⟨n, hn⟩ := h
  rcases hn with h | h
  · exact kpAbs_of_chop h
  · exact kpAbs_of_deep h

/-- **Termination of the Kirby–Paris hydra game.**  The one-move relation of the hydra game is
well founded; equivalently, there is no infinite play: for every starting hydra, every strategy
(choice of heads to chop) and every choice of regrowth parameters, the game reaches the empty
hydra after finitely many moves. -/
theorem Hydra_Kirby_Paris :
    WellFounded KPMove ∧
      ∀ (f : ℕ → Hydra) (n : ℕ → ℕ), ¬ ∀ k : ℕ, KPStep (n k) (f (k + 1)) (f k) := by
  have hwf : WellFounded KPMove :=
    Subrelation.wf (fun {a b} h => kpAbs_of_kpMove h) wellFounded_kpAbs
  refine ⟨hwf, ?_⟩
  intro f n hf
  have hstep : ∀ k : ℕ, KPMove (f (k + 1)) (f k) := fun k => ⟨n k, hf k⟩
  have key : ∀ x : Hydra, Acc KPMove x → ∀ k : ℕ, f k ≠ x := by
    intro x hx
    induction hx with
    | intro y _ ih =>
        intro k hk
        exact ih (f (k + 1)) (hk ▸ hstep k) (k + 1) rfl
  exact key (f 0) (hwf.apply _) 0 rfl

end Frontier

