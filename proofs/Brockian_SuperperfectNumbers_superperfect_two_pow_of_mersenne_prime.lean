import Mathlib

/-!
# Superperfect numbers and the Mersenne connection

For `σ(n) = ∑_{d ∣ n} d` the sum of **all** divisors of `n`, a positive integer is
**superperfect** when applying `σ` twice returns twice the number:

    σ(σ(n)) = 2n.

This is the "second-iterate" analogue of a perfect number (`σ(n) = 2n`). The structure
of the *even* superperfect numbers is completely understood, and it ties directly to the
Mersenne primes:

> **Kanold / Suryanarayana.** The even superperfect numbers are exactly the powers
> `2^{p−1}` for which `2^p − 1` is a (Mersenne) prime — e.g. `2, 4, 16, 64, …`.

whereas the *odd* case is a genuine open problem, parallel to the odd perfect number
question:

> **OPEN.** No odd superperfect number is known, and it is unknown whether one exists.

## What is a theorem here vs. what is open

Proved below (kernel-verified: no `sorry` / `admit` / `native_decide` / added axiom):

* concrete instances `superperfect_2, superperfect_4, superperfect_16, superperfect_64`
  (e.g. `σ(σ(64)) = σ(127) = 128 = 2·64`);
* the **structural direction** `superperfect_two_pow_of_mersenne_prime`: if `2 ≤ p` and
  `mersenne p = 2^p − 1` is prime, then `2^{p−1}` is superperfect. The proof runs
  `σ(2^{p−1}) = 2^p − 1 = mersenne p`, then (as `mersenne p` is prime)
  `σ(mersenne p) = mersenne p + 1 = 2^p = 2·2^{p−1}`;
* a non-example `six_not_superperfect` (`σ(σ(6)) = σ(12) = 28 ≠ 12`).

What is genuinely **open** — whether any **odd** superperfect number exists — is recorded
only as an unproven `def` `OddSuperperfectExists : Prop`. It is **neither asserted nor
denied** anywhere in this file.

## References
* Superperfect number: <https://en.wikipedia.org/wiki/Superperfect_number>
* D. Suryanarayana, *Super perfect numbers*, Elem. Math. 24 (1969), 16–17.
-/

namespace Brockian.SuperperfectNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Sum of **all** divisors of `n` (the arithmetic `σ₁`, counting `n` itself). -/
def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- **Superperfect**: applying `σ` twice doubles `n`, i.e. `σ(σ(n)) = 2n`. -/
def Superperfect (n : ℕ) : Prop := 0 < n ∧ sigma1 (sigma1 n) = 2 * n

/-- OPEN: does an **odd** superperfect number exist? **None is known** — parallel to the
odd perfect number problem. Recorded as an unproven `def`; this file neither asserts nor
denies it. -/
def OddSuperperfectExists : Prop := ∃ n : ℕ, Odd n ∧ Superperfect n

/-! ## σ-helpers -/

/-- `σ(2^k) = 2^{k+1} − 1` (the Mersenne value `2^{k+1}−1`), via the geometric-sum identity
for the divisor sum of a power of two. -/
theorem sigma_two_pow (k : ℕ) : σ 1 (2 ^ k) = 2 ^ (k + 1) - 1 := by
  simp_rw [sigma_one_apply, ← one_add_one_eq_two, ← geom_sum_mul_add 1 (k + 1)]
  norm_num

/-- For a prime `q`, `σ(q) = 1 + q` (its only divisors are `1` and `q`). -/
theorem sigma1_prime {q : ℕ} (hq : q.Prime) : sigma1 q = 1 + q := by
  rw [sigma1, hq.divisors, Finset.sum_pair hq.one_lt.ne]

/-! ## FLAGSHIP — the Mersenne connection -/

/-- **FLAGSHIP.** If `2 ≤ p` and `mersenne p = 2^p − 1` is prime, then `2^{p−1}` is
superperfect: `σ(σ(2^{p−1})) = σ(2^p − 1) = 2^p = 2·2^{p−1}`. This is the structural
theorem tying the even superperfect numbers to the Mersenne primes. -/
theorem superperfect_two_pow_of_mersenne_prime {p : ℕ} (hp : 2 ≤ p)
    (hm : (mersenne p).Prime) : Superperfect (2 ^ (p - 1)) := by
  refine ⟨by positivity, ?_⟩
  have hk : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
  -- First iterate: σ(2^{p−1}) = mersenne p = 2^p − 1.
  have h1 : sigma1 (2 ^ (p - 1)) = mersenne p := by
    rw [show sigma1 (2 ^ (p - 1)) = σ 1 (2 ^ (p - 1)) from (sigma_one_apply _).symm,
      sigma_two_pow, hk]
    rfl
  rw [h1, sigma1_prime hm]
  -- Second iterate: σ(mersenne p) = 1 + (2^p − 1) = 2^p = 2·2^{p−1}.
  have hpow : 2 ^ p = 2 * 2 ^ (p - 1) := by
    conv_lhs => rw [← hk, pow_succ]
    ring
  have hge : 1 ≤ 2 ^ p := Nat.one_le_two_pow
  unfold mersenne
  omega

/-! ## FLAGSHIP — concrete verified instances

Each `2^{p−1}` below corresponds to a Mersenne prime `2^p−1`:
`p=2→2^1=2` (`M=3`), `p=3→2^2=4` (`M=7`), `p=5→2^4=16` (`M=31`), `p=7→2^6=64` (`M=127`). -/

/-- `σ(σ(2)) = σ(3) = 4 = 2·2`. -/
theorem superperfect_2 : Superperfect 2 := ⟨by norm_num, by decide⟩

/-- `σ(σ(4)) = σ(7) = 8 = 2·4`. -/
theorem superperfect_4 : Superperfect 4 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 8000 in
/-- `σ(σ(16)) = σ(31) = 32 = 2·16`. -/
theorem superperfect_16 : Superperfect 16 := ⟨by norm_num, by decide⟩

set_option maxRecDepth 100000 in
/-- `σ(σ(64)) = σ(127) = 128 = 2·64` (`127` is the Mersenne prime `2^7−1`). -/
theorem superperfect_64 : Superperfect 64 := ⟨by norm_num, by decide⟩

/-! ## A non-example -/

set_option maxRecDepth 8000 in
/-- `6` is **not** superperfect: `σ(σ(6)) = σ(12) = 28 ≠ 12 = 2·6`. -/
theorem six_not_superperfect : ¬ Superperfect 6 := by unfold Superperfect; decide

end Brockian.SuperperfectNumbers
