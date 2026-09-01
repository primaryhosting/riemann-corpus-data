/-!
# Mergesort Correct
Category: Computer Science
Target: CS.mergesort_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- **Mergesort is correct.**

For any boolean comparison `le` that is transitive and total, `List.mergeSort le l`
is sorted with respect to `le` (expressed by `List.Pairwise`, the sortedness predicate
used by Mathlib) and is a permutation of `l`.

Both halves are supplied by existing library lemmas:
* `List.pairwise_mergeSort` (sortedness of the output),
* `List.mergeSort_perm` (the output is a permutation of the input).

Note that this file needs no `import`: `List.mergeSort` and both lemmas live in the
Lean core library, which is available automatically; the statement and proof are
unchanged in a Mathlib context (see `RequestProject/MergesortMathlib.lean`, where the
Mathlib-flavoured corollaries `CS.mergesort_correct'` and `CS.mergesort_le_correct` are
derived from this theorem). -/
theorem mergesort_correct {α : Type _} (le : α → α → Bool)
    (htrans : ∀ a b c, le a b → le b c → le a c)
    (htotal : ∀ a b, le a b || le b a)
    (l : List α) :
    List.Pairwise (fun a b => le a b = true) (l.mergeSort le) ∧
      (l.mergeSort le).Perm l :=
  ⟨List.pairwise_mergeSort htrans htotal l, List.mergeSort_perm l le⟩

end CS

import Mathlib
import RequestProject.Main

/-!
# Mergesort correctness, Mathlib phrasing

`CS.mergesort_correct` (in `RequestProject/Main.lean`) is stated with `List.Pairwise`,
the sortedness predicate used by Mathlib. Here we record the corollaries phrased for a
decidable, total, transitive `Prop`-valued relation, and the special case of `≤` on a
linear order.
-/

namespace CS

/-- Mergesort with a decidable total transitive relation `r` produces a `r`-sorted list
which is a permutation of the input. -/
theorem mergesort_correct' {α : Type*} (r : α → α → Prop) [DecidableRel r]
    [Std.Total r] [IsTrans α r] (l : List α) :
    (l.mergeSort (fun a b => decide (r a b))).Pairwise r ∧
      (l.mergeSort (fun a b => decide (r a b))).Perm l := by
  refine ⟨?_, ?_⟩
  · have h := (mergesort_correct (fun a b => decide (r a b))
      (fun a b c hab hbc => by
        simp only [decide_eq_true_eq] at hab hbc ⊢
        exact _root_.trans hab hbc)
      (fun a b => by
        rcases Std.Total.total (r := r) a b with h | h <;> simp [h])
      l).1
    simpa [List.Pairwise] using h
  · exact List.mergeSort_perm l _

/-- Mergesort on a linear order, using `≤`. -/
theorem mergesort_le_correct {α : Type*} [LinearOrder α] (l : List α) :
    (l.mergeSort (fun a b => decide (a ≤ b))).Pairwise (· ≤ ·) ∧
      (l.mergeSort (fun a b => decide (a ≤ b))).Perm l :=
  mergesort_correct' (· ≤ ·) l

end CS

