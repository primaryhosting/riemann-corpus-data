import Mathlib

def aliquot (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

def Semiperfect (n : ℕ) : Prop :=
  ∃ s ∈ n.properDivisors.powerset, ∑ d ∈ s, d = n

/-- If the aliquot sum of `n` is less than `n` (i.e. `n` is deficient), then no subset of
the proper divisors of `n` can sum to `n`, so `n` is not semiperfect. -/
theorem not_semiperfect_of_aliquot_lt {n : ℕ} (h : aliquot n < n) :
    ¬ Semiperfect n := by
  rintro ⟨s, hs, hsum⟩
  rw [Finset.mem_powerset] at hs
  have hle : ∑ d ∈ s, d ≤ ∑ d ∈ n.properDivisors, d :=
    Finset.sum_le_sum_of_subset (f := fun d => d) hs
  rw [hsum] at hle
  exact absurd (hle.trans_lt h) (lt_irrefl n)

