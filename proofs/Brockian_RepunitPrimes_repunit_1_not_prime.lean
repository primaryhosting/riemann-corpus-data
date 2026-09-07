/-
  Brockian/RepunitPrimes.lean — base-10 repunit primes, the prime-index law, and the
  open infinitude conjecture.

  The n-th base-10 repunit is R_n = (10ⁿ − 1)/9 = 11…1 (n ones). Here it is defined
  division-free as the geometric sum `∑_{i<n} 10^i`. We verify concrete instances
  (R_2 = 11 is prime; R_1, R_3, R_4, R_5, R_6 are composite), prove the classical
  structural theorem that a repunit prime must have prime index (`prime_of_repunit_prime`,
  via the divisibility law `repunit_dvd_of_dvd`), and record the OPEN infinitude question
  as an unproven `def` — it is NOT resolved here.

  Known repunit primes have prime index: R_2, R_19, R_23, R_317, R_1031, … . Whether
  there are infinitely many is a longstanding open problem.

  Verification (spec §2A triple verification):
    - local `lake build`  : see PORT-QUEUE.md
    - `#print axioms`      : [propext, Classical.choice, Quot.sound]  (clean)
    - AXLE independent     : verified @ lean-4.32.0
-/
import Mathlib

open Finset

namespace Brockian.RepunitPrimes

/-- The n-th base-10 repunit R_n = ∑_{i<n} 10^i = 11…1 (n ones). -/
def repunit (n : ℕ) : ℕ := ∑ i ∈ Finset.range n, 10 ^ i

/-- OPEN PROBLEM (recorded, NOT proved): there are infinitely many repunit primes.
This is an unproven `def` — the file never asserts it holds. -/
def RepunitPrimeInfinitude : Prop := ∀ N : ℕ, ∃ n : ℕ, N < n ∧ (repunit n).Prime

/-! ## (1) Concrete repunit prime and composites -/

/-- **R_2 = 11 is a repunit prime.** -/
theorem repunit_2_prime : (repunit 2).Prime := by
  have h : repunit 2 = 11 := by
    norm_num [repunit, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [h]; norm_num

/-- R_1 = 1 is not prime. -/
theorem repunit_1_not_prime : ¬ (repunit 1).Prime := by
  have h : repunit 1 = 1 := by
    norm_num [repunit, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [h]; norm_num

/-- R_3 = 111 = 3 · 37 is not prime. -/
theorem repunit_3_not_prime : ¬ (repunit 3).Prime := by
  have h : repunit 3 = 111 := by
    norm_num [repunit, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [h]; norm_num

/-- R_4 = 1111 = 11 · 101 is not prime. -/
theorem repunit_4_not_prime : ¬ (repunit 4).Prime := by
  have h : repunit 4 = 1111 := by
    norm_num [repunit, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [h]; norm_num

/-- R_5 = 11111 = 41 · 271 is not prime. -/
theorem repunit_5_not_prime : ¬ (repunit 5).Prime := by
  have h : repunit 5 = 11111 := by
    norm_num [repunit, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [h]; norm_num

/-- R_6 = 111111 = 3 · 7 · 11 · 13 · 37 is not prime. -/
theorem repunit_6_not_prime : ¬ (repunit 6).Prime := by
  have h : repunit 6 = 111111 := by
    norm_num [repunit, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [h]; norm_num

/-! ## (3) Strict monotonicity (helper for the structural theorem) -/

/-- The repunit sequence is strictly increasing: each extra term adds `10^i > 0`. -/
theorem repunit_strictMono : StrictMono repunit := by
  intro a b hab
  refine Finset.sum_lt_sum_of_subset (Finset.range_subset_range.mpr hab.le)
    (i := a) (Finset.mem_range.mpr hab) ?_ ?_ ?_
  · simp
  · positivity
  · intro j _ _; positivity

/-! ## (2) Divisibility and the prime-index law -/

/-- The division-free identity `R_m · 9 + 1 = 10^m`, i.e. `9 · R_m = 10^m − 1`. -/
theorem repunit_mul_nine_add_one (m : ℕ) : repunit m * 9 + 1 = 10 ^ m := by
  have h := geom_sum_mul_add (9 : ℕ) m
  simpa [repunit] using h

/-- **Divisibility law.** If `d ∣ n` then `R_d ∣ R_n` for the base-10 repunit. -/
theorem repunit_dvd_of_dvd {d n : ℕ} (h : d ∣ n) : repunit d ∣ repunit n := by
  -- 10^d − 1 ∣ 10^n − 1 from d ∣ n, then cancel the common factor 9.
  have hpow : (10 : ℕ) ^ d - 1 ∣ 10 ^ n - 1 := Nat.pow_sub_one_dvd_pow_sub_one 10 h
  have hd : (10 : ℕ) ^ d - 1 = repunit d * 9 := by
    have := repunit_mul_nine_add_one d; omega
  have hn : (10 : ℕ) ^ n - 1 = repunit n * 9 := by
    have := repunit_mul_nine_add_one n; omega
  rw [hd, hn] at hpow
  exact (mul_dvd_mul_iff_right (by norm_num : (9 : ℕ) ≠ 0)).mp hpow

/-- **Prime-index law.** If the repunit `R_n` is prime, then its index `n` is prime.
(Contrapositive: a composite index yields a nontrivial repunit factorization.) -/
theorem prime_of_repunit_prime {n : ℕ} (h : (repunit n).Prime) : n.Prime := by
  rcases lt_or_ge n 2 with hlt | hge
  · -- n = 0 (R_0 = 0) or n = 1 (R_1 = 1): the hypothesis is already false.
    interval_cases n
    · rw [show repunit 0 = 0 from by simp [repunit]] at h
      exact absurd h Nat.not_prime_zero
    · rw [show repunit 1 = 1 from by simp [repunit]] at h
      exact absurd h Nat.not_prime_one
  · -- n ≥ 2: if n were composite, R_d ∣ R_n with 1 < R_d < R_n contradicts primality.
    by_contra hn
    obtain ⟨d, hdn, hd2, hdlt⟩ := Nat.exists_dvd_of_not_prime2 hge hn
    have hdvd : repunit d ∣ repunit n := repunit_dvd_of_dvd hdn
    have hmono : repunit 2 ≤ repunit d := repunit_strictMono.monotone hd2
    have hv2 : repunit 2 = 11 := by
      norm_num [repunit, Finset.sum_range_succ, Finset.sum_range_zero]
    have h1 : 1 < repunit d := by omega
    have h2 : repunit d < repunit n := repunit_strictMono hdlt
    rcases h.eq_one_or_self_of_dvd (repunit d) hdvd with he | he
    · omega
    · omega

end Brockian.RepunitPrimes
