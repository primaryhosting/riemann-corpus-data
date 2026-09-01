import Mathlib

namespace Brockian.ZumkellerNumbers

/-- `n` is *Zumkeller* if its divisors split into two sets of equal sum, expressed via
the half-sum characterization: some subset of the divisors sums to half of sigma(n). -/
def Zumkeller (n : ℕ) : Prop :=
  ∃ S : Finset ℕ, S ⊆ n.divisors ∧ 2 * (∑ d ∈ S, d) = ∑ d ∈ n.divisors, d

/-- Every divisor of an odd number is odd. -/
lemma odd_of_dvd_odd {n d : ℕ} (hodd : Odd n) (hd : d ∣ n) : Odd d := by
  obtain ⟨c, rfl⟩ := hd
  exact (Nat.odd_mul.mp hodd).1

/-- For odd `n`, the sum of divisors has the same parity as the number of divisors. -/
lemma sum_divisors_mod_two {n : ℕ} (hodd : Odd n) :
    (∑ d ∈ n.divisors, d) % 2 = n.divisors.card % 2 := by
  rw [Finset.sum_nat_mod]
  rw [Finset.sum_congr rfl
    (fun d hd => Nat.odd_iff.mp (odd_of_dvd_odd hodd (Nat.dvd_of_mem_divisors hd)))]
  simp

/-- A nonzero square has an odd number of divisors. -/
lemma odd_card_divisors_of_isSquare {n : ℕ} (hn : n ≠ 0) (hsq : IsSquare n) :
    Odd n.divisors.card := by
  obtain ⟨k, rfl⟩ := hsq
  have hk : k ≠ 0 := by rintro rfl; simp at hn
  rw [Nat.card_divisors hn]
  refine Finset.prod_induction _ Odd (fun a b => Odd.mul) odd_one ?_
  intro p _
  have hfac : (k * k).factorization p = 2 * k.factorization p := by
    rw [Nat.factorization_mul hk hk]; simp [two_mul]
  rw [hfac]
  exact ⟨k.factorization p, by ring⟩

/-- An odd Zumkeller number is not a perfect square: being Zumkeller forces `sigma n` to be
even, while for an odd square all divisors are odd and there is an odd number of them, so
`sigma n` would be odd. -/
theorem odd_zumkeller_not_square {n : ℕ} (hodd : Odd n) (h : Zumkeller n) : ¬ IsSquare n := by
  intro hsq
  obtain ⟨S, _, hsum⟩ := h
  have hn : n ≠ 0 := by rintro rfl; simp at hodd
  have h1 : (∑ d ∈ n.divisors, d) % 2 = 0 := by omega
  have h2 := sum_divisors_mod_two hodd
  have h3 := Nat.odd_iff.mp (odd_card_divisors_of_isSquare hn hsq)
  omega

end Brockian.ZumkellerNumbers

