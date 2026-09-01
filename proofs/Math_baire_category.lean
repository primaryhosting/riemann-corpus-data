import Mathlib

/-!
# Baire Category
Category: Pure Mathematics
Target: Math.baire_category
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Baire category theorem** (union form): a nonempty complete metric space is not the
union of countably many nowhere dense subsets. -/
theorem baire_category {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (S : ℕ → Set X) (hS : ∀ n, IsNowhereDense (S n)) :
    (⋃ n, S n) ≠ Set.univ := by
  intro hunion
  have hopen : ∀ n, IsOpen (closure (S n))ᶜ := fun n => isClosed_closure.isOpen_compl
  have hdense : ∀ n, Dense (closure (S n))ᶜ := fun n =>
    interior_eq_empty_iff_dense_compl.mp (hS n)
  obtain ⟨x, hx⟩ := (dense_iInter_of_isOpen hopen hdense).nonempty
  have hxS : x ∈ ⋃ n, S n := hunion ▸ Set.mem_univ x
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hxS
  exact (Set.mem_iInter.mp hx n) (subset_closure hn)

end Math

