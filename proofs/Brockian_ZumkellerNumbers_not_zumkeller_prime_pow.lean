import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/
def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d

/-- No prime power is Zumkeller: prime powers are deficient, since
`sigma (p ^ k) = 1 + p + ⋯ + p ^ k < 2 * p ^ k`, while any Zumkeller number `m`
satisfies `2 * m ≤ sigma m` (the witnessing subset or its complement contains `m`). -/
theorem not_zumkeller_prime_pow {p k : ℕ} (hp : p.Prime) : ¬ Zumkeller (p ^ k) := by
  rintro ⟨S, hS, hsum⟩
  have hn0 : (p ^ k) ≠ 0 := pow_ne_zero _ hp.pos.ne'
  have hmem : p ^ k ∈ (p ^ k).divisors := Nat.mem_divisors_self _ hn0
  -- Any Zumkeller number is at most half of its divisor sum.
  have key : 2 * p ^ k ≤ ∑ d ∈ (p ^ k).divisors, d := by
    by_cases h : p ^ k ∈ S
    · have h1 := Finset.single_le_sum (f := fun d : ℕ => d) (fun i _ => Nat.zero_le i) h
      simp only at h1
      omega
    · have hT : p ^ k ∈ (p ^ k).divisors \ S := Finset.mem_sdiff.2 ⟨hmem, h⟩
      have hle := Finset.single_le_sum (f := fun d : ℕ => d) (fun i _ => Nat.zero_le i) hT
      have hsplit := Finset.sum_sdiff (f := fun d : ℕ => d) hS
      simp only at hle hsplit
      omega
  -- But prime powers are deficient.
  have hdiv : ∑ d ∈ (p ^ k).divisors, d = ∑ i ∈ Finset.range (k + 1), p ^ i :=
    Nat.sum_divisors_prime_pow hp
  have hgeom : ∑ i ∈ Finset.range k, p ^ i < p ^ k :=
    Nat.geomSum_lt hp.two_le fun i hi => Finset.mem_range.1 hi
  rw [Finset.sum_range_succ] at hdiv
  omega

end Brockian.ZumkellerNumbers

