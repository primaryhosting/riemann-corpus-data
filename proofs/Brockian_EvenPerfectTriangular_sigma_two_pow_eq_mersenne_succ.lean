import Mathlib

namespace Brockian.EvenPerfectTriangular

open ArithmeticFunction Finset
open scoped sigma

/-- The sum of the divisors of a power of two is the corresponding Mersenne number. -/
theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) :
    σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

/-- A positive natural number is a power of two times an odd number. -/
theorem eq_two_pow_mul_not_even {n : ℕ} (hpos : 0 < n) :
    ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.finiteMultiplicity_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
  use multiplicity 2 n, m
  refine ⟨hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose! hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

/-- Euler's classification: every even perfect number is a power of two times
its associated Mersenne prime.  This proof uses only main-library APIs. -/
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ}
    (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧
      n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  rcases eq_two_pow_mul_not_even hpos with ⟨k, m, rfl, hm⟩
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne,
    add_mul, one_mul, add_comm] at h
  have hj := add_left_cancel h
  cases Nat.sum_properDivisors_dvd
      (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  | inl h₁ =>
      have j1 : j = 1 := Eq.trans hj.symm h₁
      rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h₁
      simp [h₁, j1]
  | inr h₁ =>
      have jcon := Eq.trans hj.symm h₁
      rw [← one_mul j, ← mul_assoc, mul_one] at jcon
      have hj0 : j ≠ 0 := by
        intro hjzero
        subst j
        simp at hpos
      have jcon2 := mul_right_cancel₀ hj0 jcon
      exfalso
      match k with
      | 0 =>
        apply hm
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev
        rw [← jcon2, one_mul]
        exact even_iff_two_dvd.mp ev
      | .succ k =>
        apply ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)

/-- Every even perfect number is a triangular number. -/
theorem even_perfect_triangular {n : ℕ} (he : Even n) (hp : Nat.Perfect n) :
    ∃ k : ℕ, n = k * (k + 1) / 2 := by
  obtain ⟨p, _hprime, rfl⟩ :=
    eq_two_pow_mul_prime_mersenne_of_even_perfect he hp
  refine ⟨mersenne (p + 1), ?_⟩
  rw [mersenne]
  have hpow : 1 ≤ 2 ^ (p + 1) := one_le_pow₀ (by omega)
  rw [Nat.sub_add_cancel hpow]
  have hdiv : 2 ∣ 2 ^ (p + 1) := by
    rw [pow_succ]
    exact dvd_mul_of_dvd_right (dvd_refl 2) (2 ^ p)
  rw [Nat.mul_div_assoc _ hdiv]
  norm_num [pow_succ]
  ac_rfl

end Brockian.EvenPerfectTriangular

