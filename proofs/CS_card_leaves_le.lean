/-
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

/-- A comparison-based sorting algorithm on `n` elements, modelled as a binary decision tree.
A `node i j l r` compares the elements at positions `i` and `j`, continuing with `l` if the
`i`-th element is smaller and with `r` otherwise.  A `leaf p` outputs the permutation `p`. -/
inductive CompTree (n : ℕ) : Type where
  | leaf : Equiv.Perm (Fin n) → CompTree n
  | node : Fin n → Fin n → CompTree n → CompTree n → CompTree n

namespace CompTree

variable {n : ℕ}

/-- The worst-case number of comparisons performed, i.e. the depth of the decision tree. -/
def depth : CompTree n → ℕ
  | .leaf _ => 0
  | .node _ _ l r => max l.depth r.depth + 1

/-- Running the algorithm on the input whose ranking is described by the permutation `σ`
(the element at position `i` is smaller than the one at position `j` iff `σ i < σ j`). -/
def run : CompTree n → Equiv.Perm (Fin n) → Equiv.Perm (Fin n)
  | .leaf p, _ => p
  | .node i j l r, σ => if σ i < σ j then l.run σ else r.run σ

/-- The finite set of outputs occurring at the leaves of the tree. -/
def leaves : CompTree n → Finset (Equiv.Perm (Fin n))
  | .leaf p => {p}
  | .node _ _ l r => l.leaves ∪ r.leaves

/-- A tree with `d` levels of comparisons has at most `2 ^ d` distinct leaf outputs. -/
theorem card_leaves_le (t : CompTree n) : t.leaves.card ≤ 2 ^ t.depth := by
  induction t with
  | leaf p => simp [leaves, depth]
  | node i j l r ihl ihr =>
      refine le_trans (Finset.card_union_le _ _) ?_
      have hl : l.leaves.card ≤ 2 ^ (max l.depth r.depth) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : r.leaves.card ≤ 2 ^ (max l.depth r.depth) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc l.leaves.card + r.leaves.card
          ≤ 2 ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth) := Nat.add_le_add hl hr
        _ = 2 ^ (max l.depth r.depth + 1) := by ring
  
/-- Every output of the algorithm occurs at some leaf. -/
theorem run_mem_leaves (t : CompTree n) (σ : Equiv.Perm (Fin n)) : t.run σ ∈ t.leaves := by
  induction t with
  | leaf p => simp [run, leaves]
  | node i j l r ihl ihr =>
      by_cases h : σ i < σ j <;>
        simp [run, leaves, h, ihl, ihr]

/-- The tree is a correct comparison sort: on every input it recovers the ranking. -/
def Sorts (t : CompTree n) : Prop := ∀ σ : Equiv.Perm (Fin n), t.run σ = σ

/-- A correct comparison sort must have at least `n !` leaves. -/
theorem factorial_le_card_leaves (t : CompTree n) (h : t.Sorts) :
    n ! ≤ t.leaves.card := by
  have huniv : (Finset.univ : Finset (Equiv.Perm (Fin n))) ⊆ t.leaves := by
    intro σ _
    have := run_mem_leaves t σ
    rwa [h σ] at this
  have := Finset.card_le_card huniv
  simpa [Fintype.card_perm] using this

end CompTree

/-- **Comparison-sort lower bound for 4 elements.**
Any correct comparison sort of 4 elements needs at least `⌈log₂ (4!)⌉ = 5` comparisons
in the worst case. -/
theorem sorting_lb_4 (t : CompTree 4) (h : t.Sorts) : Nat.clog 2 (4 !) ≤ t.depth := by
  have hcard : (4 ! : ℕ) ≤ 2 ^ t.depth :=
    (CompTree.factorial_le_card_leaves t h).trans (CompTree.card_leaves_le t)
  exact Nat.clog_le_of_le_pow hcard

/-- The bound of `sorting_lb_4` is the number `5`. -/
theorem clog_two_factorial_four : Nat.clog 2 (4 !) = 5 := by
  norm_num [Nat.factorial]

/-- Restatement: any correct comparison sort of 4 elements needs at least 5 comparisons. -/
theorem sorting_lb_4' (t : CompTree 4) (h : t.Sorts) : 5 ≤ t.depth := by
  simpa [clog_two_factorial_four] using sorting_lb_4 t h

/-- Helper for writing down an explicit permutation of `Fin 4` from a function and its inverse. -/
def mkPerm (f g : Fin 4 → Fin 4) (h1 : ∀ x, g (f x) = x := by decide)
    (h2 : ∀ x, f (g x) = x := by decide) : Equiv.Perm (Fin 4) := ⟨f, g, h1, h2⟩

/-- An explicit comparison sort of 4 elements using only 5 comparisons in the worst case,
witnessing that the lower bound of `sorting_lb_4'` is attained. -/
def sortTree4 : CompTree 4 :=
  (.node 0 1
    (.node 0 2
      (.node 1 2
        (.node 1 3
          (.node 2 3
            (.leaf (mkPerm ![0, 1, 2, 3] ![0, 1, 2, 3]))
            (.leaf (mkPerm ![0, 1, 3, 2] ![0, 1, 3, 2])))
          (.node 0 3
            (.leaf (mkPerm ![0, 2, 3, 1] ![0, 3, 1, 2]))
            (.leaf (mkPerm ![1, 2, 3, 0] ![3, 0, 1, 2]))))
        (.node 2 3
          (.node 1 3
            (.leaf (mkPerm ![0, 2, 1, 3] ![0, 2, 1, 3]))
            (.leaf (mkPerm ![0, 3, 1, 2] ![0, 2, 3, 1])))
          (.node 0 3
            (.leaf (mkPerm ![0, 3, 2, 1] ![0, 3, 2, 1]))
            (.leaf (mkPerm ![1, 3, 2, 0] ![3, 0, 2, 1])))))
      (.node 0 3
        (.node 1 3
          (.leaf (mkPerm ![1, 2, 0, 3] ![2, 0, 1, 3]))
          (.leaf (mkPerm ![1, 3, 0, 2] ![2, 0, 3, 1])))
        (.node 2 3
          (.leaf (mkPerm ![2, 3, 0, 1] ![2, 3, 0, 1]))
          (.leaf (mkPerm ![2, 3, 1, 0] ![3, 2, 0, 1])))))
    (.node 0 2
      (.node 0 3
        (.node 2 3
          (.leaf (mkPerm ![1, 0, 2, 3] ![1, 0, 2, 3]))
          (.leaf (mkPerm ![1, 0, 3, 2] ![1, 0, 3, 2])))
        (.node 1 3
          (.leaf (mkPerm ![2, 0, 3, 1] ![1, 3, 0, 2]))
          (.leaf (mkPerm ![2, 1, 3, 0] ![3, 1, 0, 2]))))
      (.node 1 2
        (.node 2 3
          (.node 0 3
            (.leaf (mkPerm ![2, 0, 1, 3] ![1, 2, 0, 3]))
            (.leaf (mkPerm ![3, 0, 1, 2] ![1, 2, 3, 0])))
          (.node 1 3
            (.leaf (mkPerm ![3, 0, 2, 1] ![1, 3, 2, 0]))
            (.leaf (mkPerm ![3, 1, 2, 0] ![3, 1, 2, 0]))))
        (.node 1 3
          (.node 0 3
            (.leaf (mkPerm ![2, 1, 0, 3] ![2, 1, 0, 3]))
            (.leaf (mkPerm ![3, 1, 0, 2] ![2, 1, 3, 0])))
          (.node 2 3
            (.leaf (mkPerm ![3, 2, 0, 1] ![2, 3, 1, 0]))
            (.leaf (mkPerm ![3, 2, 1, 0] ![3, 2, 1, 0])))))))

theorem sortTree4_depth : sortTree4.depth = 5 := by decide

theorem sortTree4_sorts : sortTree4.Sorts := by
  intro σ
  revert σ
  decide

/-- The lower bound is tight: 5 comparisons are necessary and sufficient to sort 4 elements. -/
theorem sorting_opt_4 : IsLeast {d : ℕ | ∃ t : CompTree 4, t.Sorts ∧ t.depth = d} 5 :=
  ⟨⟨sortTree4, sortTree4_sorts, sortTree4_depth⟩, by
    rintro d ⟨t, ht, rfl⟩
    exact sorting_lb_4' t ht⟩

end CS

