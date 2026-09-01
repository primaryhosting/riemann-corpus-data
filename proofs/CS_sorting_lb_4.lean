import Mathlib

/-!
# Sorting Lb 4
Category: Computer Science
Target: CS.sorting_lb_4
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

set_option grind.warning false

namespace CS

/-- A comparison-based decision tree sorting `n` elements.
A `node (i, j) t f` compares the keys at positions `i` and `j`, descending into
`t` if the key at `i` is `≤` the key at `j`, and into `f` otherwise.
A `leaf p` outputs the permutation `p` describing the discovered order. -/
inductive DTree (n : ℕ) where
  | leaf : Equiv.Perm (Fin n) → DTree n
  | node : Fin n → Fin n → DTree n → DTree n → DTree n

namespace DTree

variable {n : ℕ}

/-- The worst-case number of comparisons performed by the tree. -/
def depth : DTree n → ℕ
  | leaf _ => 0
  | node _ _ t f => max (depth t) (depth f) + 1

/-- Running the decision tree on the input whose key at position `i` is `σ i`. -/
def run : DTree n → Equiv.Perm (Fin n) → Equiv.Perm (Fin n)
  | leaf p, _ => p
  | node i j t f, σ => if σ i ≤ σ j then run t σ else run f σ

/-- The (finite) set of permutations that can be output by the tree. -/
def leaves [DecidableEq (Equiv.Perm (Fin n))] : DTree n → Finset (Equiv.Perm (Fin n))
  | leaf p => {p}
  | node _ _ t f => leaves t ∪ leaves f

/-- A comparison sort is *correct* if on every input it outputs the correct order. -/
def Correct (t : DTree n) : Prop := ∀ σ : Equiv.Perm (Fin n), run t σ = σ

theorem run_mem_leaves [DecidableEq (Equiv.Perm (Fin n))] (t : DTree n)
    (σ : Equiv.Perm (Fin n)) : run t σ ∈ leaves t := by
  induction t with
  | leaf p => simp [run, leaves]
  | node i j t f iht ihf =>
      by_cases h : σ i ≤ σ j <;> simp [run, leaves, h, iht, ihf]

theorem card_leaves_le [DecidableEq (Equiv.Perm (Fin n))] (t : DTree n) :
    (leaves t).card ≤ 2 ^ depth t := by
  induction t with
  | leaf p => simp [leaves, depth]
  | node i j t f iht ihf =>
      refine le_trans (Finset.card_union_le _ _) ?_
      have h1 : (leaves t).card ≤ 2 ^ max (depth t) (depth f) :=
        iht.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have h2 : (leaves f).card ≤ 2 ^ max (depth t) (depth f) :=
        ihf.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc (leaves t).card + (leaves f).card
          ≤ 2 ^ max (depth t) (depth f) + 2 ^ max (depth t) (depth f) := by omega
        _ = 2 ^ (max (depth t) (depth f) + 1) := by ring
        _ = 2 ^ depth (node i j t f) := by rw [depth]

/-- A correct comparison sort must have at least `n !` leaves, since it must be able
to output every permutation. -/
theorem factorial_le_card_leaves [DecidableEq (Equiv.Perm (Fin n))] {t : DTree n}
    (h : Correct t) : n ! ≤ (leaves t).card := by
  have hsub : (Finset.univ : Finset (Equiv.Perm (Fin n))) ⊆ leaves t := by
    intro σ _
    have := run_mem_leaves t σ
    rwa [h σ] at this
  have := Finset.card_le_card hsub
  simpa [Fintype.card_perm] using this

/-- Sanity check that `Correct` is satisfiable: comparing the two keys correctly sorts
two elements with a single comparison. -/
theorem correct_two :
    Correct (node (n := 2) 0 1 (leaf 1) (leaf (Equiv.swap 0 1))) := by
  intro σ
  revert σ
  exact of_decide_eq_true (by rfl)

end DTree

/-- **Comparison-sort lower bound for 4 elements.**
Any correct comparison-based sorting algorithm on 4 elements, modelled as a
decision tree, performs at least `⌈log₂ (4!)⌉ = 5` comparisons in the worst case. -/
theorem sorting_lb_4 (t : DTree 4) (h : DTree.Correct t) :
    Nat.clog 2 (Nat.factorial 4) ≤ t.depth := by
  classical
  have hfac : Nat.factorial 4 = 24 := by decide
  have hclog : Nat.clog 2 (Nat.factorial 4) = 5 := by rw [hfac]; decide
  rw [hclog]
  by_contra hlt
  push_neg at hlt
  have hd : t.depth ≤ 4 := by omega
  have h1 : (24 : ℕ) ≤ (DTree.leaves t).card := by
    have := DTree.factorial_le_card_leaves h
    rwa [hfac] at this
  have h2 : (DTree.leaves t).card ≤ 2 ^ t.depth := DTree.card_leaves_le t
  have h3 : (2 : ℕ) ^ t.depth ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hd
  omega

end CS

