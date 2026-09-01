import Mathlib

/-- The aliquot sum of `n`: the sum of its proper divisors. -/
def aliquot (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

/-- `n` is semiperfect if some set of proper divisors of `n` sums to `n`. -/
def Semiperfect (n : ℕ) : Prop :=
  ∃ s ∈ n.properDivisors.powerset, ∑ d ∈ s, d = n

/-- A perfect number (aliquot sum equal to itself) is semiperfect: take the full
set of proper divisors as the witnessing subset.

The positivity hypothesis `hn` was requested in the statement but is not needed
for the proof. -/
theorem semiperfect_of_perfect {n : ℕ} (hn : 0 < n) (h : aliquot n = n) :
    Semiperfect n :=
  ⟨n.properDivisors, Finset.mem_powerset_self _, h⟩

