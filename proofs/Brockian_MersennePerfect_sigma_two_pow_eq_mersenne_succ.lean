import Mathlib

/-!
# Even perfect numbers via Euclid–Euler, and the open infinitude question

This module records the **concrete, fully verified** even perfect numbers
`6, 28, 496, 8128` together with the Mersenne primes that generate them, and it
isolates — as *unproven definitions* — the genuinely **open** statements about
their infinitude.

## What is a theorem (settled) vs. what is open

The **Euclid–Euler theorem** states: `n` is an even perfect number **iff**
`n = 2 ^ k * (2 ^ (k+1) − 1)` with `2 ^ (k+1) − 1 = mersenne (k+1)` a (Mersenne)
prime. This equivalence is a *theorem* — it is Theorem 70 of the 100-theorems
list and is formalized in Mathlib's `Archive` (`Theorems100.Nat`). Because the
`Archive` is **not** part of `import Mathlib`, the Euclid–Euler lemmas are
re-proved here from main-library API only (`mersenne` itself lives in
`Mathlib.NumberTheory.LucasLehmer`, which *is* in the main library). None of the
proofs below use `sorry`, `admit`, `native_decide`, or any added axiom.

What is genuinely **open** is whether there are *infinitely many* Mersenne primes
— equivalently, infinitely many even perfect numbers. These two open statements
are recorded below as `MersennePrimeInfinitude` / `EvenPerfectInfinitude`. They
are `def`s of type `Prop`; **neither is asserted**. The only theorem proved
*about* them (`infinitude_equiv`) is that the two open statements are equivalent
— which is itself a consequence of Euclid–Euler and does **not** decide either.

## References
* Euclid–Euler theorem: <https://en.wikipedia.org/wiki/Euclid%E2%80%93Euler_theorem>
* Mathlib `Archive/Wiedijk100Theorems/PerfectNumbers.lean` (Aaron Anderson).
-/

namespace Brockian.MersennePerfect

open ArithmeticFunction Finset
open scoped sigma

/-! ## Euclid–Euler machinery (re-proved from main-library API)

These four lemmas are ported verbatim from Mathlib's `Archive` proof of Theorem 70
(Author: Aaron Anderson). They are reproduced here only because the `Archive`
namespace is unavailable under `import Mathlib`; every step uses main-library API. -/

theorem sigma_two_pow_eq_mersenne_succ (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) := by
  simp_rw [sigma_one_apply, mersenne, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

/-- **Euclid's direction**: a Mersenne prime induces an even perfect number. -/
theorem perfect_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Nat.Perfect (2 ^ k * mersenne (k + 1)) := by
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul, ← mul_assoc, ← pow_succ', ← sigma_one_apply,
    mul_comm,
    isMultiplicative_sigma.map_mul_of_coprime ((Odd.coprime_two_right (by simp)).pow_right _),
    sigma_two_pow_eq_mersenne_succ]
  · simp [pr, sigma_one_apply]
  · positivity

theorem ne_zero_of_prime_mersenne (k : ℕ) (pr : (mersenne (k + 1)).Prime) : k ≠ 0 := by
  intro H
  simp [H, mersenne, Nat.not_prime_one] at pr

theorem even_two_pow_mul_mersenne_of_prime (k : ℕ) (pr : (mersenne (k + 1)).Prime) :
    Even (2 ^ k * mersenne (k + 1)) := by
  simp [ne_zero_of_prime_mersenne k pr, parity_simps]

theorem eq_two_pow_mul_odd {n : ℕ} (hpos : 0 < n) : ∃ k m : ℕ, n = 2 ^ k * m ∧ ¬Even m := by
  have h := Nat.finiteMultiplicity_iff.2 ⟨Nat.prime_two.ne_one, hpos⟩
  obtain ⟨m, hm⟩ := pow_multiplicity_dvd 2 n
  use multiplicity 2 n, m
  refine ⟨hm, ?_⟩
  rw [even_iff_two_dvd]
  have hg := h.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)
  contrapose hg
  rcases hg with ⟨k, rfl⟩
  apply Dvd.intro k
  rw [pow_succ, mul_assoc, ← hm]

/-- **Euler's direction**: every even perfect number is `2 ^ k · mersenne (k+1)`
with `mersenne (k+1)` prime. -/
theorem eq_two_pow_mul_prime_mersenne_of_even_perfect {n : ℕ} (ev : Even n) (perf : Nat.Perfect n) :
    ∃ k : ℕ, Nat.Prime (mersenne (k + 1)) ∧ n = 2 ^ k * mersenne (k + 1) := by
  have hpos := perf.2
  rcases eq_two_pow_mul_odd hpos with ⟨k, m, rfl, hm⟩
  use k
  rw [even_iff_two_dvd] at hm
  rw [Nat.perfect_iff_sum_divisors_eq_two_mul hpos, ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ, ← mul_assoc, ← pow_succ'] at perf
  obtain ⟨j, rfl⟩ := ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ perf)
  rw [← mul_assoc, mul_comm _ (mersenne _), mul_assoc] at perf
  have h := mul_left_cancel₀ (by positivity) perf
  rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self, ← succ_mersenne, add_mul,
    one_mul, add_comm] at h
  have hj := add_left_cancel h
  cases Nat.sum_properDivisors_dvd (by rw [hj]; apply Dvd.intro_left (mersenne (k + 1)) rfl) with
  | inl h_1 =>
    have j1 : j = 1 := Eq.trans hj.symm h_1
    rw [j1, mul_one, Nat.sum_properDivisors_eq_one_iff_prime] at h_1
    simp [h_1, j1]
  | inr h_1 =>
    have jcon := Eq.trans hj.symm h_1
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
        rw [mersenne, ← Nat.pred_eq_sub_one, Nat.lt_pred_iff, ← pow_one (Nat.succ 1)]
        apply pow_lt_pow_right₀ (Nat.lt_succ_self 1) (Nat.succ_lt_succ k.succ_pos)
    contrapose hm
    simp [hm]

/-! ## (2) The Mersenne ↔ even-perfect bridge (concrete primes) -/

theorem mersenne_2_prime : (mersenne 2).Prime := by norm_num [mersenne]
theorem mersenne_3_prime : (mersenne 3).Prime := by norm_num [mersenne]
theorem mersenne_5_prime : (mersenne 5).Prime := by norm_num [mersenne]
theorem mersenne_7_prime : (mersenne 7).Prime := by norm_num [mersenne]

/-! ## (1) FLAGSHIP: concrete even perfect numbers

Each is obtained from Euclid's direction applied to the corresponding Mersenne
prime, then the closed form `2 ^ k · mersenne (k+1)` is reduced to the literal. -/

/-- `6 = 2^1 · (2^2 − 1) = 2 · 3` is perfect. -/
theorem perfect_6 : Nat.Perfect 6 := by
  have h := perfect_two_pow_mul_mersenne_of_prime 1 mersenne_2_prime
  norm_num [mersenne] at h
  exact h

/-- `28 = 2^2 · (2^3 − 1) = 4 · 7` is perfect. -/
theorem perfect_28 : Nat.Perfect 28 := by
  have h := perfect_two_pow_mul_mersenne_of_prime 2 mersenne_3_prime
  norm_num [mersenne] at h
  exact h

/-- `496 = 2^4 · (2^5 − 1) = 16 · 31` is perfect. -/
theorem perfect_496 : Nat.Perfect 496 := by
  have h := perfect_two_pow_mul_mersenne_of_prime 4 mersenne_5_prime
  norm_num [mersenne] at h
  exact h

/-- `8128 = 2^6 · (2^7 − 1) = 64 · 127` is perfect. -/
theorem perfect_8128 : Nat.Perfect 8128 := by
  have h := perfect_two_pow_mul_mersenne_of_prime 6 mersenne_7_prime
  norm_num [mersenne] at h
  exact h

/-! ## The OPEN infinitude statements (unproven definitions)

These `Prop`-valued `def`s stand in for the open problems. They are **never
asserted** anywhere in this file. -/

/-- **OPEN**: there are infinitely many Mersenne primes — for every bound `N`
there is a prime exponent `p > N` with `mersenne p` prime. Unproven definition. -/
def MersennePrimeInfinitude : Prop := ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ (mersenne p).Prime

/-- **OPEN**: there are infinitely many even perfect numbers. Unproven definition. -/
def EvenPerfectInfinitude : Prop := ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Even n ∧ Nat.Perfect n

/-! ## (3) STRETCH: the two open statements are equivalent

This is a *conditional* theorem — it relates the two open `Prop`s via Euclid–Euler
and decides **neither**. -/

/-- The infinitude of Mersenne primes is equivalent to the infinitude of even
perfect numbers (Euclid–Euler, applied at every bound). This proves the two OPEN
statements are equivalent; it does not prove either one. -/
theorem infinitude_equiv : MersennePrimeInfinitude ↔ EvenPerfectInfinitude := by
  constructor
  · -- Mersenne prime at exponent `p > N`  ⇒  even perfect number `> N`.
    intro mpi N
    obtain ⟨p, hNp, hp, hmp⟩ := mpi N
    -- `p ≥ 1`, so write `p = (p-1) + 1` and use Euclid's direction.
    have hpk : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos hp.pos
    set k := p - 1 with hk
    have hmk : (mersenne (k + 1)).Prime := by rw [hpk]; exact hmp
    refine ⟨2 ^ k * mersenne (k + 1), ?_,
      even_two_pow_mul_mersenne_of_prime k hmk,
      perfect_two_pow_mul_mersenne_of_prime k hmk⟩
    -- `N < p ≤ 2^p - 1 = mersenne p ≤ 2^k * mersenne p = n`.
    rw [hpk]
    have hpm : p ≤ mersenne p := by
      have := p.lt_two_pow_self
      simp only [mersenne]; omega
    have hle : mersenne p ≤ 2 ^ k * mersenne p :=
      Nat.le_mul_of_pos_left _ (by positivity)
    omega
  · -- even perfect number `> 4^N`  ⇒  Mersenne prime at exponent `> N`.
    intro epi N
    obtain ⟨n, hMn, hev, hperf⟩ := epi (4 ^ N)
    obtain ⟨k, hkprime, rfl⟩ := eq_two_pow_mul_prime_mersenne_of_even_perfect hev hperf
    refine ⟨k + 1, ?_, Nat.Prime.of_mersenne hkprime, hkprime⟩
    -- `n = 2^k · mersenne (k+1) < 4^(k+1)`, and `4^N < n`, so `4^N < 4^(k+1)`.
    have h1 : mersenne (k + 1) < 2 ^ (k + 1) :=
      Nat.sub_lt (by positivity) one_pos
    have key : 2 ^ k * mersenne (k + 1) < 4 ^ (k + 1) := by
      calc 2 ^ k * mersenne (k + 1)
          < 2 ^ k * 2 ^ (k + 1) := by gcongr
        _ = 2 ^ (k + (k + 1)) := by rw [← pow_add]
        _ ≤ 2 ^ (2 * (k + 1)) := by
              apply Nat.pow_le_pow_right (by norm_num); omega
        _ = 4 ^ (k + 1) := by rw [pow_mul]; norm_num
    have hlt : 4 ^ N < 4 ^ (k + 1) := lt_trans hMn key
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt

end Brockian.MersennePerfect
