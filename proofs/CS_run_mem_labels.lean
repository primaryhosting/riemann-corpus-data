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

/-- A comparison-based decision tree for sorting 4 elements.  A `node i j l r`
compares the keys at positions `i` and `j`, continuing in `l` if the key at `i`
is smaller and in `r` otherwise.  A `leaf p` announces that the input ordering
is the permutation `p`. -/
inductive DTree : Type
  | leaf : Equiv.Perm (Fin 4) → DTree
  | node : Fin 4 → Fin 4 → DTree → DTree → DTree
  deriving Inhabited

namespace DTree

/-- The worst-case number of comparisons performed by a decision tree. -/
def depth : DTree → ℕ
  | leaf _ => 0
  | node _ _ l r => max (depth l) (depth r) + 1

/-- Running the tree on the input whose key at position `i` is `σ i`. -/
def run : DTree → Equiv.Perm (Fin 4) → Equiv.Perm (Fin 4)
  | leaf p, _ => p
  | node i j l r, σ => if σ i < σ j then run l σ else run r σ

/-- The (finite) set of answers the tree can possibly output. -/
def labels : DTree → Finset (Equiv.Perm (Fin 4))
  | leaf p => {p}
  | node _ _ l r => labels l ∪ labels r

theorem run_mem_labels (t : DTree) (σ : Equiv.Perm (Fin 4)) :
    run t σ ∈ labels t := by
  induction t with
  | leaf p => simp [run, labels]
  | node i j l r ihl ihr =>
      by_cases h : σ i < σ j <;> simp [run, labels, h, ihl, ihr]

theorem card_labels_le (t : DTree) : (labels t).card ≤ 2 ^ depth t := by
  induction t with
  | leaf p => simp [labels, depth]
  | node i j l r ihl ihr =>
      have h := Finset.card_union_le (labels l) (labels r)
      have hl : (labels l).card ≤ 2 ^ (max (depth l) (depth r)) :=
        ihl.trans (Nat.pow_le_pow_right (by norm_num) (le_max_left _ _))
      have hr : (labels r).card ≤ 2 ^ (max (depth l) (depth r)) :=
        ihr.trans (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))
      calc (labels (node i j l r)).card ≤ (labels l).card + (labels r).card := h
        _ ≤ 2 ^ (max (depth l) (depth r)) + 2 ^ (max (depth l) (depth r)) := by omega
        _ = 2 ^ depth (node i j l r) := by rw [depth, pow_succ]; ring

end DTree

/-- **Comparison-sort lower bound for 4 elements.**  Any comparison-based
decision tree that correctly determines the ordering of 4 elements (i.e. on the
input given by the permutation `σ` it outputs `σ`) must, in the worst case,
perform at least `⌈log₂ (4!)⌉ = 5` comparisons. -/
theorem sorting_lb_4 (t : DTree) (hcorrect : ∀ σ : Equiv.Perm (Fin 4), t.run σ = σ) :
    Nat.clog 2 (Nat.factorial 4) ≤ t.depth := by
  have hsub : (Finset.univ : Finset (Equiv.Perm (Fin 4))) ⊆ t.labels := by
    intro σ _
    have := t.run_mem_labels σ
    rwa [hcorrect σ] at this
  have hcard : Nat.factorial 4 ≤ (t.labels).card := by
    have h1 : (Finset.univ : Finset (Equiv.Perm (Fin 4))).card = Nat.factorial 4 := by
      simp [Finset.card_univ, Fintype.card_perm]
    calc Nat.factorial 4 = (Finset.univ : Finset (Equiv.Perm (Fin 4))).card := h1.symm
      _ ≤ (t.labels).card := Finset.card_le_card hsub
  have hpow : Nat.factorial 4 ≤ 2 ^ t.depth := hcard.trans (DTree.card_labels_le t)
  exact (Nat.clog_le_iff_le_pow (by norm_num)).mpr hpow

/-- The bound in `CS.sorting_lb_4` really is `5` comparisons. -/
theorem clog_factorial_four : Nat.clog 2 (Nat.factorial 4) = 5 := by
  norm_num [Nat.factorial]

/-- Build a permutation of `Fin 4` from a function together with its inverse. -/
def perm4 (f g : Fin 4 → Fin 4) (h1 : ∀ x, g (f x) = x) (h2 : ∀ x, f (g x) = x) :
    Equiv.Perm (Fin 4) := ⟨f, g, h1, h2⟩

/-- An optimal comparison-sorting decision tree for 4 elements, of depth `5`. -/
def optTree : DTree :=
  (CS.DTree.node 0 1
    (CS.DTree.node 0 2
      (CS.DTree.node 1 2
        (CS.DTree.node 1 3
          (CS.DTree.node 2 3
            (CS.DTree.leaf (CS.perm4 ![0,1,2,3] ![0,1,2,3] (by decide) (by decide)))
            (CS.DTree.leaf (CS.perm4 ![0,1,3,2] ![0,1,3,2] (by decide) (by decide))))
          (CS.DTree.node 0 3
            (CS.DTree.leaf (CS.perm4 ![0,2,3,1] ![0,3,1,2] (by decide) (by decide)))
            (CS.DTree.leaf (CS.perm4 ![1,2,3,0] ![3,0,1,2] (by decide) (by decide)))))
        (CS.DTree.node 2 3
          (CS.DTree.node 1 3
            (CS.DTree.leaf (CS.perm4 ![0,2,1,3] ![0,2,1,3] (by decide) (by decide)))
            (CS.DTree.leaf (CS.perm4 ![0,3,1,2] ![0,2,3,1] (by decide) (by decide))))
          (CS.DTree.node 0 3
            (CS.DTree.leaf (CS.perm4 ![0,3,2,1] ![0,3,2,1] (by decide) (by decide)))
            (CS.DTree.leaf (CS.perm4 ![1,3,2,0] ![3,0,2,1] (by decide) (by decide))))))
      (CS.DTree.node 0 3
        (CS.DTree.node 1 3
          (CS.DTree.leaf (CS.perm4 ![1,2,0,3] ![2,0,1,3] (by decide) (by decide)))
          (CS.DTree.leaf (CS.perm4 ![1,3,0,2] ![2,0,3,1] (by decide) (by decide))))
        (CS.DTree.node 2 3
          (CS.DTree.leaf (CS.perm4 ![2,3,0,1] ![2,3,0,1] (by decide) (by decide)))
          (CS.DTree.leaf (CS.perm4 ![2,3,1,0] ![3,2,0,1] (by decide) (by decide))))))
    (CS.DTree.node 0 2
      (CS.DTree.node 0 3
        (CS.DTree.node 2 3
          (CS.DTree.leaf (CS.perm4 ![1,0,2,3] ![1,0,2,3] (by decide) (by decide)))
          (CS.DTree.leaf (CS.perm4 ![1,0,3,2] ![1,0,3,2] (by decide) (by decide))))
        (CS.DTree.node 1 3
          (CS.DTree.leaf (CS.perm4 ![2,0,3,1] ![1,3,0,2] (by decide) (by decide)))
          (CS.DTree.leaf (CS.perm4 ![2,1,3,0] ![3,1,0,2] (by decide) (by decide)))))
      (CS.DTree.node 1 2
        (CS.DTree.node 2 3
          (CS.DTree.node 0 3
            (CS.DTree.leaf (CS.perm4 ![2,0,1,3] ![1,2,0,3] (by decide) (by decide)))
            (CS.DTree.leaf (CS.perm4 ![3,0,1,2] ![1,2,3,0] (by decide) (by decide))))
          (CS.DTree.node 1 3
            (CS.DTree.leaf (CS.perm4 ![3,0,2,1] ![1,3,2,0] (by decide) (by decide)))
            (CS.DTree.leaf (CS.perm4 ![3,1,2,0] ![3,1,2,0] (by decide) (by decide)))))
        (CS.DTree.node 1 3
          (CS.DTree.node 0 3
            (CS.DTree.leaf (CS.perm4 ![2,1,0,3] ![2,1,0,3] (by decide) (by decide)))
            (CS.DTree.leaf (CS.perm4 ![3,1,0,2] ![2,1,3,0] (by decide) (by decide))))
          (CS.DTree.node 2 3
            (CS.DTree.leaf (CS.perm4 ![3,2,0,1] ![2,3,1,0] (by decide) (by decide)))
            (CS.DTree.leaf (CS.perm4 ![3,2,1,0] ![3,2,1,0] (by decide) (by decide))))))))

theorem optTree_depth : optTree.depth = 5 := by decide

theorem optTree_correct : ∀ σ : Equiv.Perm (Fin 4), optTree.run σ = σ := by decide

/-- The lower bound of `CS.sorting_lb_4` is attained: some comparison sort of 4
elements uses exactly `⌈log₂ (4!)⌉ = 5` comparisons in the worst case. -/
theorem sorting_lb_4_tight :
    ∃ t : DTree, (∀ σ : Equiv.Perm (Fin 4), t.run σ = σ) ∧
      t.depth = Nat.clog 2 (Nat.factorial 4) :=
  ⟨optTree, optTree_correct, by rw [optTree_depth, clog_factorial_four]⟩

end CS

