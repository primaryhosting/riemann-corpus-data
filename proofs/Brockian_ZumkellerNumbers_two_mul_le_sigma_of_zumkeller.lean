import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/
def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d

/-- Every Zumkeller number is perfect or abundant: `2 * n ≤ σ(n)`. -/
theorem two_mul_le_sigma_of_zumkeller {n : ℕ} (hn : 0 < n) (h : Zumkeller n) :
    2 * n ≤ ∑ d ∈ n.divisors, d := by
  obtain ⟨S, hS, hsum⟩ := h
  have hnd : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
  have hsplit : (∑ d ∈ n.divisors \ S, d) + (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d :=
    Finset.sum_sdiff hS
  by_cases hmem : n ∈ S
  · have : n ≤ ∑ d ∈ S, d :=
      Finset.single_le_sum (f := fun d => d) (by intros; positivity) hmem
    omega
  · have hmem' : n ∈ n.divisors \ S := Finset.mem_sdiff.2 ⟨hnd, hmem⟩
    have : n ≤ ∑ d ∈ n.divisors \ S, d :=
      Finset.single_le_sum (f := fun d => d) (by intros; positivity) hmem'
    omega

end Brockian.ZumkellerNumbers

