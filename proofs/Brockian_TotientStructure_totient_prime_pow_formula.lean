/-
  Brockian/TotientStructure.lean — general structural theorems for Euler's
  totient function φ.

  These are GENERAL φ-structure theorems (not concrete numerical instances):
  they pin down the qualitative behaviour of Euler's totient `φ n = Nat.totient n`
  (the number of integers in `[0, n)` coprime to `n`). This file adds a φ-layer to
  complement the existing σ/τ structural layer (`DivisorSumStructure`,
  `DivisorCountStructure`).

  Contents:
    * `gauss_sum_totient`             — **Gauss's divisor-sum identity**:
        `∑_{d ∣ n} φ(d) = n`. Thin re-export of `Nat.sum_totient`.
    * `totient_prime_sub_one`         — `φ(p) = p − 1` for `p` prime. Thin
        re-export of `Nat.totient_prime` (the base case referenced below).
    * `totient_eq_sub_one_iff_prime`  — **characterization of primes**:
        for `n ≥ 2`, `φ(n) = n − 1 ↔ n` is prime. Curated interface over
        `Nat.totient_eq_iff_prime` with the natural `2 ≤ n` hypothesis.
    * `totient_prime_pow_formula`     — `φ(p^k) = p^k − p^(k−1)` for `p` prime,
        `k ≥ 1`. Genuinely proved: rewrites `Nat.totient_prime_pow`
        (`φ(p^k) = p^(k−1)·(p−1)`) into the subtractive closed form.
    * `totient_even_of_three_le`      — `φ(n)` is even for `n ≥ 3`. Curated
        interface over `Nat.totient_even`.
    * `totient_lt_self_of_two_le`     — `φ(n) < n` for `n ≥ 2` (`n` is not coprime
        to itself). Curated interface over `Nat.totient_lt`.

  Uses CORE Mathlib only (`φ = Nat.totient`). No `sorry`, `admit`,
  `native_decide`, or `axiom` is used anywhere in this file.

  Verification:
    - AXLE independent : verified @ lean-4.32.0
-/
import Mathlib

open Finset

namespace Brockian.TotientStructure

/-- **Gauss's divisor-sum identity for φ.** Summing Euler's totient over the
divisors of `n` recovers `n` itself: `∑_{d ∣ n} φ(d) = n`. -/
theorem gauss_sum_totient (n : ℕ) : ∑ d ∈ n.divisors, Nat.totient d = n :=
  Nat.sum_totient n

/-- **φ of a prime.** `φ(p) = p − 1` for prime `p`: every residue `1, …, p−1` is
coprime to `p`. This is the base case for the prime-power formula and the
primality characterization below. -/
theorem totient_prime_sub_one {p : ℕ} (hp : p.Prime) : Nat.totient p = p - 1 :=
  Nat.totient_prime hp

/-- **Primality characterization via φ.** For `n ≥ 2`, `φ(n) = n − 1` iff `n` is
prime. A number `n ≥ 2` is prime exactly when *every* smaller positive residue is
coprime to it. -/
theorem totient_eq_sub_one_iff_prime {n : ℕ} (hn : 2 ≤ n) :
    Nat.totient n = n - 1 ↔ n.Prime :=
  Nat.totient_eq_iff_prime (by omega)

/-- **Prime-power formula.** For prime `p` and `k ≥ 1`,
`φ(p^k) = p^k − p^(k−1)`. Proved from `Nat.totient_prime_pow`
(`φ(p^k) = p^(k−1)·(p−1)`) by expanding the product into the subtractive
closed form. -/
theorem totient_prime_pow_formula {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    Nat.totient (p ^ k) = p ^ k - p ^ (k - 1) := by
  have hpk : p ^ (k - 1) * p = p ^ k := by
    rw [← pow_succ]; congr 1; omega
  have key : ∀ a b : ℕ, a * (b - 1) = a * b - a := by
    intro a b
    cases b with
    | zero => simp
    | succ m => rw [Nat.succ_sub_one, Nat.mul_succ, Nat.add_sub_cancel]
  rw [Nat.totient_prime_pow hp hk, key, hpk]

/-- **φ is even for `n ≥ 3`.** For any `n ≥ 3`, `φ(n)` is even: coprime residues
pair up under `x ↦ n − x`. -/
theorem totient_even_of_three_le {n : ℕ} (hn : 3 ≤ n) : Even (Nat.totient n) :=
  Nat.totient_even (by omega)

/-- **φ is strictly below the identity for `n ≥ 2`.** `φ(n) < n` whenever
`n ≥ 2`, because `n` itself is not coprime to `n` (so at least one residue is
excluded from the count). -/
theorem totient_lt_self_of_two_le {n : ℕ} (hn : 2 ≤ n) : Nat.totient n < n :=
  Nat.totient_lt n (by omega)

end Brockian.TotientStructure
