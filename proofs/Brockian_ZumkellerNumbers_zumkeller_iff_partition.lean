import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/
def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d

/-- The half-sum characterization of Zumkeller numbers is equivalent to the
equal-partition form: a subset of the divisors whose sum equals the sum of its complement. -/
theorem zumkeller_iff_partition (n : ℕ) :
    Zumkeller n ↔ ∃ S ⊆ n.divisors, ∑ d ∈ S, d = ∑ d ∈ n.divisors \ S, d := by
  constructor
  · rintro ⟨S, hS, h⟩
    have hsum : (∑ d ∈ n.divisors \ S, d) + ∑ d ∈ S, d = ∑ d ∈ n.divisors, d :=
      Finset.sum_sdiff hS
    exact ⟨S, hS, by omega⟩
  · rintro ⟨S, hS, h⟩
    have hsum : (∑ d ∈ n.divisors \ S, d) + ∑ d ∈ S, d = ∑ d ∈ n.divisors, d :=
      Finset.sum_sdiff hS
    exact ⟨S, hS, by omega⟩

end Brockian.ZumkellerNumbers

