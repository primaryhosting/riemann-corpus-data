import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

/-- A comparison-based decision tree for sorting 3 elements.

An input is a permutation `s : Equiv.Perm (Fin 3)`, thought of as assigning to each
position `i` its rank `s i`.  An internal node `node i j l r` compares the keys at
positions `i` and `j`, descending into `l` if `s i < s j` and into `r` otherwise.
A leaf outputs a permutation, the algorithm's claimed ranking of the input. -/
inductive DTree where
  | leaf : Equiv.Perm (Fin 3) → DTree
  | node : Fin 3 → Fin 3 → DTree → DTree → DTree

namespace DTree

/-- The worst-case number of comparisons performed by the tree, i.e. its height. -/
def depth : DTree → ℕ
  | .leaf _ => 0
  | .node _ _ l r => 1 + max l.depth r.depth

/-- Running the decision tree on an input ranking `s`. -/
def run : DTree → Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3)
  | .leaf p, _ => p
  | .node i j l r, s => if s i < s j then l.run s else r.run s

/-- The list of outputs sitting at the leaves of the tree. -/
def leaves : DTree → List (Equiv.Perm (Fin 3))
  | .leaf p => [p]
  | .node _ _ l r => l.leaves ++ r.leaves

lemma run_mem_leaves (t : DTree) (s : Equiv.Perm (Fin 3)) : t.run s ∈ t.leaves := by
  induction t with
  | leaf p => simp [run, leaves]
  | node i j l r ihl ihr =>
      by_cases h : s i < s j <;> simp [run, leaves, h, ihl, ihr]

lemma length_leaves_le (t : DTree) : t.leaves.length ≤ 2 ^ t.depth := by
  induction t with
  | leaf p => simp [leaves, depth]
  | node i j l r ihl ihr =>
      have h1 : l.leaves.length ≤ 2 ^ (max l.depth r.depth) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have h2 : r.leaves.length ≤ 2 ^ (max l.depth r.depth) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      have : l.leaves.length + r.leaves.length ≤ 2 ^ (max l.depth r.depth) +
          2 ^ (max l.depth r.depth) := Nat.add_le_add h1 h2
      have hp : 2 ^ (1 + max l.depth r.depth)
          = 2 ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth) := by
        rw [pow_add, pow_one]; ring
      simpa [leaves, depth, hp] using this

end DTree

/-- A decision tree *sorts* if on every input ranking it outputs that ranking. -/
def Sorts (t : DTree) : Prop := ∀ s : Equiv.Perm (Fin 3), t.run s = s

/-- **Comparison-sorting lower bound for 3 elements.**
Any comparison-based decision tree that correctly sorts 3 elements performs at least
`⌈log₂ (3!)⌉ = 3` comparisons in the worst case. -/
theorem sorting_lb_3 (t : DTree) (h : Sorts t) : Nat.clog 2 (Nat.factorial 3) ≤ t.depth := by
  classical
  have hsub : (Finset.univ : Finset (Equiv.Perm (Fin 3))) ⊆ t.leaves.toFinset := by
    intro s _
    have := t.run_mem_leaves s
    rw [h s] at this
    simpa using this
  have hcard : (6 : ℕ) ≤ t.leaves.toFinset.card := by
    have h6 : (Finset.univ : Finset (Equiv.Perm (Fin 3))).card = 6 := by
      simp [Finset.card_univ, Fintype.card_perm, Nat.factorial]
    calc (6 : ℕ) = (Finset.univ : Finset (Equiv.Perm (Fin 3))).card := h6.symm
      _ ≤ t.leaves.toFinset.card := Finset.card_le_card hsub
  have hlen : (6 : ℕ) ≤ 2 ^ t.depth :=
    hcard.trans ((List.toFinset_card_le _).trans t.length_leaves_le)
  have hclog : Nat.clog 2 (Nat.factorial 3) = 3 := by decide
  rw [hclog]
  by_contra hlt
  interval_cases hd : t.depth <;> omega

/-- The bound is attained: there is a comparison tree that sorts 3 elements using
exactly `⌈log₂ (3!)⌉ = 3` comparisons in the worst case.  In particular the lower
bound `CS.sorting_lb_3` is not vacuous. -/
theorem sorting_lb_3_tight :
    ∃ t : DTree, Sorts t ∧ t.depth = Nat.clog 2 (Nat.factorial 3) := by
  refine ⟨.node 0 1
      (.node 1 2 (.leaf 1)
        (.node 0 2 (.leaf (Equiv.swap 1 2)) (.leaf (Equiv.swap 0 1 * Equiv.swap 1 2))))
      (.node 0 2 (.leaf (Equiv.swap 0 1))
        (.node 1 2 (.leaf (Equiv.swap 1 2 * Equiv.swap 0 1)) (.leaf (Equiv.swap 0 2)))),
    ?_, ?_⟩
  · intro s
    revert s
    decide
  · decide

end CS

