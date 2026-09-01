import Mathlib

namespace Brockian.EvenPerfectMod9

open ArithmeticFunction Finset
open scoped sigma

/-- The sum of the divisors of a power of two is the corresponding Mersenne number.
This is a main-library reconstruction of the ingredient needed for Euclid--Euler. -/
theorem sigma_two_pow_eq_mersenne_succ_main (k : ℕ) :
    σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two,
    ← geom_sum_mul_add 1 (k + 1)]
  norm_num

/-- Every positive natural number is a power of two times an odd number. -/
theorem eq_two_pow_mul_odd_main {n : ℕ} (hpos : 0 < n) :
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

/-- Euler's classification of even perfect numbers, reconstructed using only
main-library APIs. -/
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect_main {n : ℕ}
    (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧
      n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  rcases eq_two_pow_mul_odd_main hpos with ⟨k, m, rfl, hm⟩
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ_main, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self,
    ← succ_mersenne, add_mul, one_mul, add_comm] at h
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
    have jcon2 := mul_right_cancel₀ ?_ jcon
    · exfalso
      match k with
      | 0 =>
        apply hm
        rw [← jcon2, pow_zero, one_mul, one_mul] at ev
        rw [← jcon2, one_mul]
        exact even_iff_two_dvd.mp ev
      | .succ k =>
        apply ne_of_lt _ jcon2
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff,
          ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)
    contrapose! hm
    simp [hm]

/-- A Mersenne prime with exponent `k+1`, beyond the exceptional exponent two,
forces `k` to be even. -/
theorem even_index_of_prime_mersenne {k : ℕ}
    (hk : 1 < k) (hp : Nat.Prime (mersenne (k + 1))) : Even k := by
  have hpk : Nat.Prime (k + 1) := hp.of_mersenne
  have hn : ¬ Even (k + 1) := by
    rw [hpk.even_iff]
    omega
  rw [Nat.even_add_one] at hn
  exact Classical.byContradiction hn

/-- The Euclid--Euler expression has residue one modulo nine at every even index. -/
theorem even_euclid_euler_mod9 {k : ℕ} (hk : Even k) :
    (2 ^ k * mersenne (k + 1)) % 9 = 1 := by
  have residue (q r : ℕ) (hr : r = 0 ∨ r = 2 ∨ r = 4) :
      (2 ^ (6 * q + r) * mersenne (6 * q + r + 1)) % 9 = 1 := by
    have hbase : Nat.ModEq 9 (2 ^ 6) 1 := by norm_num
    have hpow0 : Nat.ModEq 9 (2 ^ (6 * q)) 1 := by
      rw [pow_mul]
      simpa using hbase.pow q
    rcases hr with rfl | rfl | rfl
    · have hnext : Nat.ModEq 9 (2 ^ (6 * q + 0 + 1)) 2 := by
        rw [show 6 * q + 0 + 1 = 6 * q + 1 by omega, pow_add]
        exact hpow0.mul (show Nat.ModEq 9 (2 ^ 1) 2 by norm_num)
      have hm : Nat.ModEq 9 (mersenne (6 * q + 0 + 1)) 1 := by
        rw [mersenne]
        exact Nat.ModEq.sub (c := 1) (d := 1)
          (Nat.one_le_pow _ _ (by norm_num)) (by omega) hnext (by rfl)
      simpa using hpow0.mul hm
    · have hpow : Nat.ModEq 9 (2 ^ (6 * q + 2)) 4 := by
        rw [pow_add]
        exact hpow0.mul (show Nat.ModEq 9 (2 ^ 2) 4 by norm_num)
      have hnext : Nat.ModEq 9 (2 ^ (6 * q + 2 + 1)) 8 := by
        rw [show 6 * q + 2 + 1 = 6 * q + 3 by omega, pow_add]
        exact hpow0.mul (show Nat.ModEq 9 (2 ^ 3) 8 by norm_num)
      have hm : Nat.ModEq 9 (mersenne (6 * q + 2 + 1)) 7 := by
        rw [mersenne]
        exact Nat.ModEq.sub (c := 1) (d := 1)
          (Nat.one_le_pow _ _ (by norm_num)) (by omega) hnext (by rfl)
      exact hpow.mul hm
    · have hpow : Nat.ModEq 9 (2 ^ (6 * q + 4)) 7 := by
        rw [pow_add]
        exact hpow0.mul (show Nat.ModEq 9 (2 ^ 4) 7 by norm_num)
      have hnext : Nat.ModEq 9 (2 ^ (6 * q + 4 + 1)) 5 := by
        rw [show 6 * q + 4 + 1 = 6 * q + 5 by omega, pow_add]
        exact hpow0.mul (show Nat.ModEq 9 (2 ^ 5) 5 by norm_num)
      have hm : Nat.ModEq 9 (mersenne (6 * q + 4 + 1)) 4 := by
        rw [mersenne]
        exact Nat.ModEq.sub (c := 1) (d := 1)
          (Nat.one_le_pow _ _ (by norm_num)) (by omega) hnext (by rfl)
      exact hpow.mul hm
  obtain ⟨t, rfl⟩ := hk
  have ht := Nat.mod_add_div t 3
  have hlt := Nat.mod_lt t (by norm_num : 0 < 3)
  interval_cases hrem : t % 3
  · have heq : t + t = 6 * (t / 3) + 0 := by omega
    rw [heq]
    exact residue (t / 3) 0 (Or.inl rfl)
  · have heq : t + t = 6 * (t / 3) + 2 := by omega
    rw [heq]
    exact residue (t / 3) 2 (Or.inr (Or.inl rfl))
  · have heq : t + t = 6 * (t / 3) + 4 := by omega
    rw [heq]
    exact residue (t / 3) 4 (Or.inr (Or.inr rfl))

/-- Every even perfect number greater than 6 is congruent to 1 modulo 9. -/
theorem even_perfect_mod9 {n : ℕ} (he : Even n) (hp : Nat.Perfect n) (h6 : 6 < n) :
    n % 9 = 1 := by
  obtain ⟨k, hprime, rfl⟩ :=
    eq_two_pow_mul_prime_mersenne_of_even_perfect_main he hp
  apply even_euclid_euler_mod9
  apply even_index_of_prime_mersenne (hp := hprime)
  by_contra hnot
  interval_cases k <;> norm_num [mersenne] at h6

end Brockian.EvenPerfectMod9

