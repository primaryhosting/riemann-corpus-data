/-
  Brockian/MultiperfectStructure.lean — GENERAL structural theorems for the
  multiperfect (k-perfect) numbers.

  For `σ(n) = ∑_{d ∣ n} d` the sum of **all** divisors of `n` (the arithmetic
  function `ArithmeticFunction.sigma 1`, NOT a nonexistent `Nat.sigma`), a
  positive integer `n` is **k-perfect** (multiperfect of order `k`) when

      σ(n) = k · n.

  The case `k = 2` is the ordinary perfect numbers; `k = 3, 4, …` give the
  higher multiperfect numbers (`120`, `672`, `523776`, `30240`, …). Only
  finitely many multiperfect numbers are presently known, and whether infinitely
  many `k`-perfect numbers exist for any fixed `k ≥ 3` is a **genuine open
  problem**. The `def MultiperfectInfinitude` at the end records that open
  question WITHOUT proving it.

  Everything actually stated as a `theorem` below is a TRUE, general STRUCTURAL
  fact and is kernel-verified — no `sorry` / `admit` / `native_decide` / added
  `axiom`; the only kernel axioms are the Mathlib standard `propext,
  Classical.choice, Quot.sound`.

  Proved (all general, no numerical specialization):
    1. `multiperfect_one_iff`  — the ONLY 1-perfect number is `1`
       (`σ(n) = n ⟺ n = 1`, since for `n ≥ 2` the distinct divisors `1` and `n`
       force `σ(n) ≥ n + 1 > n`).
    2. `multiperfect_two_iff_perfect` — `2`-perfect is exactly `Nat.Perfect`
       (via the Mathlib bridge `Nat.perfect_iff_sum_divisors_eq_two_mul`).
    3. `multiperfect_ge_two_not_deficient` — a `k`-perfect number with `k ≥ 2` is
       never deficient (`σ(n) = kn ≥ 2n` forces the proper-divisor sum `≥ n`).
    4. `not_multiperfect_prime_ge_two` — no prime is `k`-perfect for `k ≥ 2`
       (`σ(p) = p + 1 < 2p ≤ kp`).

  Conventions / Mathlib facts used:
    * `ArithmeticFunction.sigma_one_apply : σ 1 n = ∑ d ∈ n.divisors, d`
    * `Nat.perfect_iff_sum_divisors_eq_two_mul (0 < n) :`
        `Nat.Perfect n ↔ ∑ d ∈ n.divisors, d = 2 * n`
    * `Nat.sum_divisors_eq_sum_properDivisors_add_self`
    * `Nat.Deficient n := ∑ i ∈ n.properDivisors, i < n`

  Verification: AXLE independent @ lean-4.32.0.
-/
import Mathlib

namespace Brockian.MultiperfectStructure

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- **Multiperfect (k-perfect).** `n` is `k`-perfect when the sum of ALL its
divisors equals `k · n`, i.e. `σ(n) = k·n`. `k = 2` is perfect; `k ≥ 3` gives the
higher multiperfect numbers. -/
def Multiperfect (k n : ℕ) : Prop := ArithmeticFunction.sigma 1 n = k * n

/-- **The only 1-perfect number is `1`.** For `n > 0`, `σ(n) = n` iff `n = 1`:
for `n ≥ 2` the divisor `1` is a *proper* divisor, so the proper-divisor sum is
`≥ 1 > 0`, forcing `σ(n) = (proper sum) + n > n`. -/
theorem multiperfect_one_iff {n : ℕ} (hn : 0 < n) : Multiperfect 1 n ↔ n = 1 := by
  unfold Multiperfect
  rw [sigma_one_apply, one_mul]
  constructor
  · intro h
    by_contra hne
    have hn2 : 2 ≤ n := by omega
    have hsplit : ∑ d ∈ n.divisors, d = ∑ d ∈ n.properDivisors, d + n :=
      Nat.sum_divisors_eq_sum_properDivisors_add_self
    have hprop0 : ∑ d ∈ n.properDivisors, d = 0 := by omega
    have h1mem : (1 : ℕ) ∈ n.properDivisors :=
      Nat.mem_properDivisors.mpr ⟨one_dvd n, hn2⟩
    have hle : (1 : ℕ) ≤ ∑ d ∈ n.properDivisors, d :=
      Finset.single_le_sum (fun i _ => Nat.zero_le i) h1mem
    omega
  · rintro rfl
    decide

/-- **2-perfect is exactly perfect.** For `n > 0`, `σ(n) = 2n` iff `Nat.Perfect n`
(the Mathlib bridge lemma). -/
theorem multiperfect_two_iff_perfect {n : ℕ} (hn : 0 < n) :
    Multiperfect 2 n ↔ Nat.Perfect n := by
  unfold Multiperfect
  rw [sigma_one_apply]
  exact (Nat.perfect_iff_sum_divisors_eq_two_mul hn).symm

/-- **A k-perfect number with `k ≥ 2` is never deficient.** From `σ(n) = k·n` and
`σ(n) = (proper-divisor sum) + n` we get the proper-divisor sum `= (k−1)·n ≥ n`,
so it is not `< n`. -/
theorem multiperfect_ge_two_not_deficient {k n : ℕ} (hk : 2 ≤ k) (hn : 0 < n)
    (h : Multiperfect k n) : ¬ Nat.Deficient n := by
  unfold Multiperfect at h
  rw [sigma_one_apply] at h
  have hsplit : ∑ d ∈ n.divisors, d = ∑ d ∈ n.properDivisors, d + n :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  have hk_n : 2 * n ≤ k * n := mul_le_mul_right' hk n
  intro hdef
  have hlt : ∑ d ∈ n.properDivisors, d < n := hdef
  omega

/-- **No prime is k-perfect for `k ≥ 2`.** A prime `p` has `σ(p) = 1 + p`, but
`k`-perfection needs `σ(p) = k·p ≥ 2p`, forcing `1 + p ≥ 2p`, i.e. `p ≤ 1` —
impossible for a prime. -/
theorem not_multiperfect_prime_ge_two {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) :
    ¬ Multiperfect k p := by
  intro h
  unfold Multiperfect at h
  rw [sigma_one_apply] at h
  have hsig : ∑ d ∈ p.divisors, d = 1 + p := by
    rw [hp.divisors, Finset.sum_pair hp.one_lt.ne]
  rw [hsig] at h
  have hk_p : 2 * p ≤ k * p := mul_le_mul_right' hk p
  have hp2 : 2 ≤ p := hp.two_le
  omega

/-- OPEN: for a fixed `k`, are there infinitely many `k`-perfect numbers? For
`k ≥ 3` this is **unknown** — only finitely many multiperfect numbers are known
at all. Recorded as an unproven `def`; this file neither asserts nor denies it. -/
def MultiperfectInfinitude (k : ℕ) : Prop := {n | Multiperfect k n}.Infinite

end Brockian.MultiperfectStructure
