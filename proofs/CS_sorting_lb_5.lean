/-
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-- A comparison-based decision tree over `5` elements returning results of type `α`.
A `node i j l r` compares the input entries at positions `i` and `j`, continuing in `l`
if the `i`-th entry is smaller and in `r` otherwise. -/
inductive DTree (α : Type*) where
  | leaf : α → DTree α
  | node : Fin 5 → Fin 5 → DTree α → DTree α → DTree α

namespace DTree

variable {α : Type*}

/-- The worst-case number of comparisons performed by the tree. -/
def depth : DTree α → ℕ
  | leaf _ => 0
  | node _ _ l r => max (depth l) (depth r) + 1

/-- Running the decision tree on an input whose ordering is described by the permutation `p`
(the input entry at position `i` has rank `p i`). -/
def eval (p : Equiv.Perm (Fin 5)) : DTree α → α
  | leaf a => a
  | node i j l r => if p i < p j then eval p l else eval p r

/-- The list of leaf labels of the tree, left to right. -/
def leaves : DTree α → List α
  | leaf a => [a]
  | node _ _ l r => leaves l ++ leaves r

lemma eval_mem_leaves (p : Equiv.Perm (Fin 5)) (t : DTree α) : t.eval p ∈ t.leaves := by
  induction t with
  | leaf a => simp [eval, leaves]
  | node i j l r ihl ihr =>
      by_cases h : p i < p j <;> simp [eval, leaves, h, ihl, ihr]

lemma length_leaves_le_two_pow (t : DTree α) : t.leaves.length ≤ 2 ^ t.depth := by
  induction t with
  | leaf a => simp [leaves, depth]
  | node i j l r ihl ihr =>
      have hl : l.leaves.length ≤ 2 ^ (max l.depth r.depth) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : r.leaves.length ≤ 2 ^ (max l.depth r.depth) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      simp only [leaves, depth, List.length_append, pow_succ]
      omega

end DTree

/-- **Comparison-sort lower bound for 5 elements.**
Any comparison-based decision tree that correctly determines the ordering of `5` elements
(i.e. on every input ordering `p` it outputs `p`) must have worst-case depth at least
`⌈log₂ (5!)⌉ = 7`. -/
theorem sorting_lb_5 (t : DTree (Equiv.Perm (Fin 5)))
    (hcorrect : ∀ p : Equiv.Perm (Fin 5), t.eval p = p) :
    Nat.clog 2 (Nat.factorial 5) ≤ t.depth := by
  classical
  -- The `5!` permutations inject into the leaf labels of `t`.
  have hmaps : Set.MapsTo (fun p : Equiv.Perm (Fin 5) => t.eval p)
      ↑(Finset.univ : Finset (Equiv.Perm (Fin 5))) ↑t.leaves.toFinset := by
    intro p _
    simpa using t.eval_mem_leaves p
  have hinj : Set.InjOn (fun p : Equiv.Perm (Fin 5) => t.eval p)
      ↑(Finset.univ : Finset (Equiv.Perm (Fin 5))) := by
    intro p _ q _ h
    simpa [hcorrect p, hcorrect q] using h
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin 5))).card ≤ t.leaves.toFinset.card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  have hfac : (Finset.univ : Finset (Equiv.Perm (Fin 5))).card = Nat.factorial 5 := by
    simp [Finset.card_univ, Fintype.card_perm]
  have key : Nat.factorial 5 ≤ 2 ^ t.depth :=
    hfac ▸ hcard.trans ((List.toFinset_card_le _).trans (t.length_leaves_le_two_pow))
  exact (Nat.clog_le_iff_le_pow (by norm_num)).2 key

/-- The bound is exactly `7`: `⌈log₂ (5!)⌉ = 7`. -/
theorem clog_two_factorial_five : Nat.clog 2 (Nat.factorial 5) = 7 := by
  norm_num [Nat.factorial]

/-- Explicit numerical form of the lower bound: at least `7` comparisons are needed in the
worst case to sort `5` elements. -/
theorem sorting_lb_5_seven (t : DTree (Equiv.Perm (Fin 5)))
    (hcorrect : ∀ p : Equiv.Perm (Fin 5), t.eval p = p) :
    7 ≤ t.depth :=
  clog_two_factorial_five ▸ sorting_lb_5 t hcorrect

end CS

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

