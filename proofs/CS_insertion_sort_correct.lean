/-
# Insertion Sort Correct
Category: Computer Science
Target: CS.insertion_sort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 400000
set_option autoImplicit false

namespace CS

/-- **Insertion sort is correct**: for a decidable, total, transitive relation `r`,
`List.insertionSort r l` is sorted with respect to `r` (i.e. its elements are pairwise
related by `r`) and is a permutation of the input list `l`.

The two components follow from Mathlib's `List.pairwise_insertionSort` and
`List.perm_insertionSort`. -/
theorem insertion_sort_correct {α : Type*} (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r] (l : List α) :
    List.Pairwise r (List.insertionSort r l) ∧ (List.insertionSort r l).Perm l :=
  ⟨List.pairwise_insertionSort r l, List.perm_insertionSort r l⟩

/-- Specialisation to `≤` on a linear order: `insertionSort (· ≤ ·)` sorts and permutes. -/
theorem insertion_sort_correct_le {α : Type*} [LinearOrder α] (l : List α) :
    List.Pairwise (· ≤ ·) (List.insertionSort (· ≤ ·) l) ∧
      (List.insertionSort (· ≤ ·) l).Perm l :=
  insertion_sort_correct (· ≤ ·) l

end CS

