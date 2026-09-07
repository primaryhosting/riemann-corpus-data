import Mathlib

/-!
# 509203 is a Riesel number (via its covering set)

A **Riesel number** is an odd `k` such that `k · 2^n − 1` is composite for every
`n ≥ 1`.  In 1956 Hans Riesel proved that infinitely many such `k` exist, and `509203`
is the **smallest known** one.  The proof is a *covering congruence* argument: the finite
set of primes

  `{3, 5, 7, 13, 17, 241}`

is a **covering set** for `k = 509203`.  The order of `2` modulo each of these primes
divides `24` (they are `2, 4, 3, 12, 8, 24`), so `2^n mod p` depends only on `n mod 24`;
and one checks the finite table that for every residue `r < 24` at least one of the six
primes divides `509203 · 2^r − 1`.  Hence for *every* `n` some prime in the set divides
`509203 · 2^n − 1`, which — being larger than the prime — is therefore composite.

This file proves the genuine unconditional theorem `riesel_509203 : IsRiesel 509203`.

## The open problem

Whether `509203` is the **smallest** Riesel number is the **open Riesel problem**:
candidates below it have not all been eliminated (the search is driven by the *PrimeGrid*
distributed project).  We record this only as an unproven `def`, `RieselProblem`; nothing
in this file asserts or resolves it.

## Main results

* `two_pow_periodic`   — periodicity of `2^n mod p` with period `24` when `2^24 ≡ 1 [MOD p]`.
* `covering_table`     — the decidable finite covering table over residues `r < 24`.
* `riesel_509203`      — **flagship**: `509203` is a Riesel number.
* `RieselProblem`      — the OPEN smallest-Riesel question (unproven `def`).

The Riesel value `k · 2^n − 1` is written with **Nat subtraction**; for `n ≥ 1` we have
`k · 2^n ≥ 2`, so `k · 2^n − 1` is well-behaved and divisibility is handled throughout via
the congruence `k · 2^n ≡ 1 [MOD p]` (equivalently `p ∣ k · 2^n − 1`), using
`Nat.modEq_iff_dvd'`.
-/

namespace Brockian.RieselCovering

/-- A **Riesel number**: an odd `k` such that `k · 2^n − 1` is composite for all
`n ≥ 1`. -/
def IsRiesel (k : ℕ) : Prop := Odd k ∧ ∀ n : ℕ, 1 ≤ n → ¬ (k * 2 ^ n - 1).Prime

/-- The **Riesel problem** (OPEN): is `509203` the smallest Riesel number?
This is recorded as an unproven `def`; it is **not** proved anywhere in this file, and
nothing here bears on its truth. -/
def RieselProblem : Prop := ∀ k : ℕ, 0 < k → k < 509203 → ¬ IsRiesel k

/-! ### (1) Periodicity of `2^n mod p` -/

/-- **Periodicity lemma.**  If `2^24 ≡ 1 [MOD p]` then `2^n ≡ 2^(n % 24) [MOD p]` for
every `n`.  This is the engine that reduces the infinitely many exponents `n` to the
finite residue table `r < 24`: writing `n = 24·(n / 24) + n % 24` and using
`(2^24)^(n/24) ≡ 1`, the high part collapses. -/
theorem two_pow_periodic {p : ℕ} (hp : 2 ^ 24 ≡ 1 [MOD p]) (n : ℕ) :
    2 ^ n ≡ 2 ^ (n % 24) [MOD p] := by
  conv_lhs => rw [← Nat.div_add_mod n 24, pow_add, pow_mul]
  calc (2 ^ 24) ^ (n / 24) * 2 ^ (n % 24)
      ≡ 1 ^ (n / 24) * 2 ^ (n % 24) [MOD p] := (hp.pow _).mul_right _
    _ = 2 ^ (n % 24) := by rw [one_pow, one_mul]

/-! ### (2) The finite covering table -/

/-- **Covering table.**  For every residue `r < 24`, at least one of the six primes in
the covering set `{3, 5, 7, 13, 17, 241}` divides `509203 · 2^r − 1`.  This is a finite,
purely decidable fact (`24` residues × `6` primes); `decide` computes each modulus. -/
theorem covering_table (r : ℕ) (hr : r < 24) :
    ∃ p ∈ ([3, 5, 7, 13, 17, 241] : List ℕ), (509203 * 2 ^ r - 1) % p = 0 := by
  revert hr r
  decide

/-! ### (3) The main theorem -/

/-- For a fixed exponent `n ≥ 1`: if a prime `p ≤ 241` with `2^24 ≡ 1 [MOD p]` divides the
residue value `509203 · 2^(n % 24) − 1`, then it divides `509203 · 2^n − 1`, which is
therefore composite (it exceeds the divisor `p`). -/
theorem composite_of {p n : ℕ} (hn : 1 ≤ n) (hpp : p.Prime) (hple : p ≤ 241)
    (hmod : 2 ^ 24 ≡ 1 [MOD p]) (hr0 : (509203 * 2 ^ (n % 24) - 1) % p = 0) :
    ¬ (509203 * 2 ^ n - 1).Prime := by
  -- Both residue and full values are `≥ 1`, so Nat subtraction is well-behaved.
  have h1r : 1 ≤ 509203 * 2 ^ (n % 24) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h1n : 1 ≤ 509203 * 2 ^ n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- `p` divides the residue value, i.e. `509203·2^(n%24) ≡ 1 [MOD p]`.
  have hpdvd_r : p ∣ (509203 * 2 ^ (n % 24) - 1) := Nat.dvd_of_mod_eq_zero hr0
  have hcong_r : 509203 * 2 ^ (n % 24) ≡ 1 [MOD p] :=
    ((Nat.modEq_iff_dvd' h1r).mpr hpdvd_r).symm
  -- Periodicity transfers the congruence from the residue exponent to `n`.
  have hper : 2 ^ n ≡ 2 ^ (n % 24) [MOD p] := two_pow_periodic hmod n
  have hcong : 509203 * 2 ^ n ≡ 1 [MOD p] :=
    (hper.mul_left 509203).trans hcong_r
  -- Hence `p ∣ 509203·2^n − 1`.
  have hpdvd : p ∣ (509203 * 2 ^ n - 1) :=
    (Nat.modEq_iff_dvd' h1n).mp hcong.symm
  -- The value strictly exceeds `241 ≥ p`, so a prime divisor `p` is a proper divisor.
  intro hN
  have h2n : (2 : ℕ) ≤ 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hmul : 509203 * 2 ≤ 509203 * 2 ^ n := Nat.mul_le_mul (le_refl 509203) h2n
  have hNbig : 241 < 509203 * 2 ^ n - 1 := by omega
  rcases (Nat.Prime.eq_one_or_self_of_dvd hN p hpdvd) with h1 | hself
  · exact hpp.ne_one h1
  · omega

/-- **Flagship theorem.**  `509203` is a Riesel number: it is odd, and `509203 · 2^n − 1`
is composite for every `n ≥ 1`.

Proof: `509203` is odd by computation.  For the compositeness, fix `n ≥ 1`, let
`r = n % 24 < 24`, and read off from `covering_table` a prime `p ∈ {3,5,7,13,17,241}`
with `p ∣ 509203 · 2^r − 1`.  Each such `p` is prime, is `≤ 241`, and satisfies
`2^24 ≡ 1 [MOD p]`; `composite_of` then transfers divisibility to `509203 · 2^n − 1` and
concludes it is not prime. -/
theorem riesel_509203 : IsRiesel 509203 := by
  refine ⟨by decide, ?_⟩
  intro n hn
  have hr : n % 24 < 24 := Nat.mod_lt n (by norm_num)
  obtain ⟨p, hpmem, hpdvd0⟩ := covering_table (n % 24) hr
  -- `p` is one of the six covering primes; each case is concrete.
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hpmem
  rcases hpmem with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact composite_of hn (by norm_num) (by norm_num) (by decide) hpdvd0

end Brockian.RieselCovering
