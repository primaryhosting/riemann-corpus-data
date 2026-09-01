import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/
def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d

/-- 6 is a Zumkeller number: `{1, 2, 3} ⊆ divisors 6` and `2 * (1 + 2 + 3) = 12 = σ(6)`. -/
theorem zumkeller_six : Zumkeller 6 := by
  refine ⟨{1, 2, 3}, ?_, ?_⟩ <;> decide

end Brockian.ZumkellerNumbers

