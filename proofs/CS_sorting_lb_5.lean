/-
# Sorting Lb 5
Category: Computer Science
Target: CS.sorting_lb_5
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
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

/-- A comparison-based sorting algorithm on `n` elements, modelled as a binary
decision tree.  A `leaf p` reports that the input order is described by the
permutation `p`; a `node i j l r` compares the `i`-th and `j`-th input entries
and continues in the left subtree if `aᵢ < a_j`, in the right subtree otherwise. -/
inductive DTree (n : ℕ) : Type
  | leaf : Equiv.Perm (Fin n) → DTree n
  | node : Fin n → Fin n → DTree n → DTree n → DTree n

namespace DTree

variable {n : ℕ}

/-- The number of comparisons performed in the worst case, i.e. the height of the tree. -/
def depth : DTree n → ℕ
  | leaf _ => 0
  | node _ _ l r => max l.depth r.depth + 1

/-- Running the decision tree on an input whose relative order is given by the
permutation `σ` (the `i`-th input entry has rank `σ i`).  The result is the
permutation reported by the leaf that is reached. -/
def run : DTree n → Equiv.Perm (Fin n) → Equiv.Perm (Fin n)
  | leaf p, _ => p
  | node i j l r, σ => if σ i < σ j then l.run σ else r.run σ

/-- A decision tree of depth `d` can produce at most `2 ^ d` distinct outputs. -/
theorem card_image_run_le (t : DTree n) :
    (Finset.univ.image t.run).card ≤ 2 ^ t.depth := by
  induction t with
  | leaf p =>
      refine le_trans (Finset.card_le_card ?_) (by simp : ({p} : Finset (Equiv.Perm (Fin n))).card ≤ 2 ^ (0 : ℕ))
      intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨σ, -, rfl⟩ := hx
      simp [run]
  | node i j l r ihl ihr =>
      have hsub : Finset.univ.image (node i j l r).run ⊆
          (Finset.univ.image l.run) ∪ (Finset.univ.image r.run) := by
        intro x hx
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨σ, rfl⟩ := hx
        by_cases h : σ i < σ j <;>
          simp [run, h, Finset.mem_union, Finset.mem_image]
      calc (Finset.univ.image (node i j l r).run).card
          ≤ ((Finset.univ.image l.run) ∪ (Finset.univ.image r.run)).card :=
            Finset.card_le_card hsub
        _ ≤ (Finset.univ.image l.run).card + (Finset.univ.image r.run).card :=
            Finset.card_union_le _ _
        _ ≤ 2 ^ l.depth + 2 ^ r.depth := Nat.add_le_add ihl ihr
        _ ≤ 2 ^ (max l.depth r.depth) + 2 ^ (max l.depth r.depth) :=
            Nat.add_le_add (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
              (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
        _ = 2 ^ (max l.depth r.depth + 1) := by ring
        _ = 2 ^ (node i j l r).depth := rfl

/-- `t` is a *correct* comparison sort: on every input order it reports that order. -/
def Correct (t : DTree n) : Prop := ∀ σ : Equiv.Perm (Fin n), t.run σ = σ

/-- A correct comparison sort must be able to output all `n!` permutations, hence
`n ! ≤ 2 ^ depth`. -/
theorem factorial_le_two_pow_depth {t : DTree n} (h : t.Correct) : n ! ≤ 2 ^ t.depth := by
  have himg : Finset.univ.image t.run = (Finset.univ : Finset (Equiv.Perm (Fin n))) := by
    apply Finset.eq_univ_of_forall
    intro σ
    exact Finset.mem_image.2 ⟨σ, Finset.mem_univ _, h σ⟩
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = n ! := by
    simp [Finset.card_univ, Fintype.card_perm]
  calc n ! = (Finset.univ.image t.run).card := by rw [himg, hcard]
    _ ≤ 2 ^ t.depth := card_image_run_le t

end DTree

/-- **Comparison-sort lower bound for 5 elements.**
Any correct comparison-based sorting algorithm on 5 elements performs at least
`⌈log₂ (5!)⌉ = 7` comparisons in the worst case. -/
theorem sorting_lb_5 (t : DTree 5) (h : t.Correct) : Nat.clog 2 (5 !) ≤ t.depth := by
  have hfac : (5 : ℕ)! = 120 := by decide
  have hle : (120 : ℕ) ≤ 2 ^ t.depth := by
    have := DTree.factorial_le_two_pow_depth h
    rwa [hfac] at this
  have h7 : 7 ≤ t.depth := by
    by_contra hcon
    push_neg at hcon
    interval_cases hd : t.depth <;> omega
  have : Nat.clog 2 (5 !) = 7 := by
    rw [hfac]
    norm_num [Nat.clog]
  omega

/-- Sanity check that the model is not vacuous: a correct comparison sort on two
elements exists, using a single comparison. -/
theorem exists_correct_two :
    ∃ t : DTree 2, t.Correct ∧ t.depth = 1 :=
  ⟨DTree.node 0 1 (DTree.leaf 1) (DTree.leaf (Equiv.swap 0 1)),
    by intro σ; revert σ; decide, rfl⟩

/-- The bound is exactly `7 = ⌈log₂ 120⌉`. -/
theorem clog_two_factorial_five : Nat.clog 2 (5 !) = 7 := by
  have hfac : (5 : ℕ)! = 120 := by decide
  rw [hfac]
  norm_num [Nat.clog]

end CS

