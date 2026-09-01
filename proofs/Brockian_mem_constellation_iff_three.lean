/-
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Constellation Local Count K 3
Category: Brockian Corpus
Target: Brockian.ConstellationLocalCountK3
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

namespace Brockian

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The local constellation count of order `k` of a finite set `A` in an abelian group:
the number of pairs `(x, d)` such that the `k`-term arithmetic progression
`x, x + d, …, x + (k-1) • d` lies entirely in `A`. -/
def constellationLocalCount (A : Finset G) (k : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : G × G => ∀ i < k, p.1 + i • p.2 ∈ A)).card

omit [Fintype G] [DecidableEq G] in
/-- Membership characterisation of the `k = 3` constellation condition. -/
lemma mem_constellation_iff_three (A : Finset G) (x d : G) :
    (∀ i < 3, x + i • d ∈ A) ↔ x ∈ A ∧ x + d ∈ A ∧ x + (2 : ℕ) • d ∈ A := by
  constructor
  · intro h
    refine ⟨?_, ?_, h 2 (by norm_num)⟩
    · simpa using h 0 (by norm_num)
    · simpa using h 1 (by norm_num)
  · rintro ⟨h0, h1, h2⟩ i hi
    interval_cases i
    · simpa using h0
    · simpa using h1
    · exact h2

/-- The `k = 3` local constellation count as a count over pairs, with the progression
condition written out explicitly. -/
lemma constellationLocalCount_three_eq_filter (A : Finset G) :
    constellationLocalCount A 3 =
      (Finset.univ.filter
        (fun p : G × G => p.1 ∈ A ∧ p.1 + p.2 ∈ A ∧ p.1 + (2 : ℕ) • p.2 ∈ A)).card := by
  unfold constellationLocalCount
  congr 1
  apply Finset.filter_congr
  intro p _
  simpa using mem_constellation_iff_three A p.1 p.2

/-- **Constellation local count, `k = 3`.** The number of `3`-term progressions
`(x, x + d, x + 2d)` contained in a finite set `A` of an abelian group is obtained by
summing, over all common differences `d`, the number of `x ∈ A` with `x + d ∈ A` and
`x + 2d ∈ A`.

The proof reduces the cardinality to a double sum of indicators
(`Finset.card_filter`, `Fintype.sum_prod_type`) and exchanges the order of summation
(`Finset.sum_comm`). -/
theorem ConstellationLocalCountK3 (A : Finset G) :
    constellationLocalCount A 3 =
      ∑ d : G, (A.filter (fun x => x + d ∈ A ∧ x + (2 : ℕ) • d ∈ A)).card := by
  rw [constellationLocalCount_three_eq_filter]
  rw [Finset.card_filter]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.card_filter, ← Finset.sum_subset (Finset.subset_univ A) (by intro x _ hx; simp [hx])]
  exact Finset.sum_congr rfl fun x hx => by simp [hx]

/-- The local constellation count is antitone in `k`: longer progressions are rarer.
In particular the `k = 3` count is at most the `k = 2` count. -/
theorem constellationLocalCount_three_le_two (A : Finset G) :
    constellationLocalCount A 3 ≤ constellationLocalCount A 2 := by
  refine Finset.card_le_card fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact fun i hi => hp i (by omega)

/-- Trivial (`d = 0`) constellations give the lower bound `|A| ≤` the `k = 3` count. -/
theorem card_le_constellationLocalCount_three (A : Finset G) :
    A.card ≤ constellationLocalCount A 3 := by
  rw [ConstellationLocalCountK3]
  calc A.card = (A.filter (fun x => x + (0 : G) ∈ A ∧ x + (2 : ℕ) • (0 : G) ∈ A)).card := by
        rw [Finset.filter_true_of_mem (by intro x hx; simpa using hx)]
    _ ≤ ∑ d : G, (A.filter (fun x => x + d ∈ A ∧ x + (2 : ℕ) • d ∈ A)).card :=
        Finset.single_le_sum (f := fun d : G =>
          (A.filter (fun x => x + d ∈ A ∧ x + (2 : ℕ) • d ∈ A)).card)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)

end Brockian

