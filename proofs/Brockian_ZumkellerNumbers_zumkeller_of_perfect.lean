import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/
def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d

/-- Every perfect number is Zumkeller: take `S = {n}`. -/
theorem zumkeller_of_perfect {n : ℕ} (hn : 0 < n) (h : ∑ d ∈ n.divisors, d = 2 * n) :
    Zumkeller n := by
  refine ⟨{n}, ?_, ?_⟩
  · simpa using Nat.mem_divisors_self n hn.ne'
  · simp [h]

end Brockian.ZumkellerNumbers

