import Mathlib

/-!
# 78557 is a Sierpiński number (via its covering set)

A **Sierpiński number** is an odd `k` such that `k · 2^n + 1` is composite for every
`n ≥ 1`.  In 1960 Wacław Sierpiński proved that infinitely many such `k` exist, and
`78557` is the **smallest known** one.  The proof is a *covering congruence* argument due
to John Selfridge (1962): the finite set of primes

  `{3, 5, 7, 13, 19, 37, 73}`

is a **covering set** for `k = 78557`.  The order of `2` modulo each of these primes
divides `36` (they are `2, 4, 3, 12, 18, 36, 9`), so `2^n mod p` depends only on
`n mod 36`; and one checks the finite table that for every residue `r < 36` at least one
of the seven primes divides `78557 · 2^r + 1`.  Hence for *every* `n` some prime in the
set divides `78557 · 2^n + 1`, which — being larger than the prime — is therefore
composite.

This file proves the genuine unconditional theorem `sierpinski_78557 : IsSierpinski 78557`.

## The open problem

Whether `78557` is the **smallest** Sierpiński number is the **open Sierpiński problem**:
candidates below it (the last few were driven to a handful by the *Seventeen or Bust* /
*PrimeGrid* distributed searches) have not all been eliminated.  We record this only as an
unproven `def`, `SierpinskiProblem`; nothing in this file asserts or resolves it.

## Main results

* `two_pow_periodic`   — periodicity of `2^n mod p` with period `36` when `2^36 ≡ 1 [MOD p]`.
* `covering_table`     — the decidable finite covering table over residues `r < 36`.
* `sierpinski_78557`   — **flagship**: `78557` is a Sierpiński number.
* `SierpinskiProblem`  — the OPEN smallest-Sierpiński question (unproven `def`).
-/

namespace Brockian.SierpinskiCovering

/-- A **Sierpiński number**: an odd `k` such that `k · 2^n + 1` is composite for all
`n ≥ 1`. -/
def IsSierpinski (k : ℕ) : Prop := Odd k ∧ ∀ n : ℕ, 1 ≤ n → ¬ (k * 2 ^ n + 1).Prime

/-- The **Sierpiński problem** (OPEN): is `78557` the smallest Sierpiński number?
This is recorded as an unproven `def`; it is **not** proved anywhere in this file, and
nothing here bears on its truth. -/
def SierpinskiProblem : Prop := ∀ k : ℕ, 0 < k → k < 78557 → ¬ IsSierpinski k

/-! ### (1) Periodicity of `2^n mod p` -/

/-- **Periodicity lemma.**  If `2^36 ≡ 1 [MOD p]` then `2^n ≡ 2^(n % 36) [MOD p]` for
every `n`.  This is the engine that reduces the infinitely many exponents `n` to the
finite residue table `r < 36`: writing `n = 36·(n / 36) + n % 36` and using
`(2^36)^(n/36) ≡ 1`, the high part collapses. -/
theorem two_pow_periodic {p : ℕ} (hp : 2 ^ 36 ≡ 1 [MOD p]) (n : ℕ) :
    2 ^ n ≡ 2 ^ (n % 36) [MOD p] := by
  conv_lhs => rw [← Nat.div_add_mod n 36, pow_add, pow_mul]
  calc (2 ^ 36) ^ (n / 36) * 2 ^ (n % 36)
      ≡ 1 ^ (n / 36) * 2 ^ (n % 36) [MOD p] := (hp.pow _).mul_right _
    _ = 2 ^ (n % 36) := by rw [one_pow, one_mul]

/-! ### (2) The finite covering table -/

/-- **Covering table.**  For every residue `r < 36`, at least one of the seven primes in
the covering set `{3, 5, 7, 13, 19, 37, 73}` divides `78557 · 2^r + 1`.  This is a finite,
purely decidable fact (`36` residues × `7` primes); `decide` computes each modulus. -/
theorem covering_table (r : ℕ) (hr : r < 36) :
    ∃ p ∈ ([3, 5, 7, 13, 19, 37, 73] : List ℕ), (78557 * 2 ^ r + 1) % p = 0 := by
  revert hr r
  decide

/-! ### (3) The main theorem -/

/-- For a fixed exponent `n ≥ 1`: if a prime `p ≤ 73` with `2^36 ≡ 1 [MOD p]` divides the
residue value `78557 · 2^(n % 36) + 1`, then it divides `78557 · 2^n + 1`, which is
therefore composite (it exceeds the divisor `p`). -/
theorem composite_of {p n : ℕ} (hn : 1 ≤ n) (hpp : p.Prime) (hple : p ≤ 73)
    (hmod : 2 ^ 36 ≡ 1 [MOD p]) (hr0 : (78557 * 2 ^ (n % 36) + 1) % p = 0) :
    ¬ (78557 * 2 ^ n + 1).Prime := by
  -- `p` divides the residue value, i.e. `78557·2^(n%36)+1 ≡ 0 [MOD p]`.
  have hpdvd_r : (78557 * 2 ^ (n % 36) + 1) ≡ 0 [MOD p] :=
    (Nat.modEq_zero_iff_dvd).mpr (Nat.dvd_of_mod_eq_zero hr0)
  -- Periodicity transfers the congruence from the residue exponent to `n`.
  have hper : 2 ^ n ≡ 2 ^ (n % 36) [MOD p] := two_pow_periodic hmod n
  have hcong : 78557 * 2 ^ n + 1 ≡ 78557 * 2 ^ (n % 36) + 1 [MOD p] :=
    (hper.mul_left 78557).add_right 1
  -- Hence `p ∣ 78557·2^n + 1`.
  have hpdvd : p ∣ (78557 * 2 ^ n + 1) :=
    (Nat.modEq_zero_iff_dvd).mp (hcong.trans hpdvd_r)
  -- The value strictly exceeds `73 ≥ p`, so a prime divisor `p` is a proper divisor.
  intro hN
  have h2n : (2 : ℕ) ≤ 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hmul : 78557 * 2 ≤ 78557 * 2 ^ n := Nat.mul_le_mul (le_refl 78557) h2n
  have hNbig : 73 < 78557 * 2 ^ n + 1 := by omega
  rcases (Nat.Prime.eq_one_or_self_of_dvd hN p hpdvd) with h1 | hself
  · exact hpp.ne_one h1
  · omega

/-- **Flagship theorem.**  `78557` is a Sierpiński number: it is odd, and `78557 · 2^n + 1`
is composite for every `n ≥ 1`.

Proof: `78557` is odd by computation.  For the compositeness, fix `n ≥ 1`, let
`r = n % 36 < 36`, and read off from `covering_table` a prime `p ∈ {3,5,7,13,19,37,73}`
with `p ∣ 78557 · 2^r + 1`.  Each such `p` is prime, is `≤ 73`, and satisfies
`2^36 ≡ 1 [MOD p]`; `composite_of` then transfers divisibility to `78557 · 2^n + 1` and
concludes it is not prime. -/
theorem sierpinski_78557 : IsSierpinski 78557 := by
  refine ⟨by decide, ?_⟩
  intro n hn
  have hr : n % 36 < 36 := Nat.mod_lt n (by norm_num)
  obtain ⟨p, hpmem, hpdvd0⟩ := covering_table (n % 36) hr
  -- `p` is one of the seven covering primes; each case is concrete.
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hpmem
  rcases hpmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact composite_of hn (by norm_num) (by norm_num) (by decide) hpdvd0

end Brockian.SierpinskiCovering
