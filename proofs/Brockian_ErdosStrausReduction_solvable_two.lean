import Mathlib

/-!
# Erdős–Straus reduction to primes `≡ 1 (mod 24)`

REDUCTION-EQUIVALENCE (CONDITIONAL): the main theorem below proves an unconditional
equivalence `A ↔ B`; **both sides remain OPEN** — this is an honest reduction of the
Erdős–Straus conjecture to its hard residue class, **NOT** a resolution of it.

`ErdosStrausConjecture` is a well-known open problem.  What is proved here, unconditionally
and axiom-cleanly, is:

* explicit parametric solutions for `n` even, `3 ∣ n`, `n ≡ 3 (mod 4)`, `n ≡ 2 (mod 3)`
  and `n ≡ 5 (mod 8)`;
* `solvable_of_mod_24_ne_one`: the conjecture holds for every `n ≥ 2` with `n % 24 ≠ 1`;
* `ErdosStrausConjecture`: the full conjecture is *equivalent* to its special case for
  primes `p ≡ 1 (mod 24)` — the sole residue class that remains open.
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

namespace Brockian.ErdosStrausReduction

/-- `Solvable n` says that `4 / n` can be written as a sum of three (not necessarily
distinct) positive unit fractions. -/
def Solvable (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-- **The Erdős–Straus conjecture**: for every integer `n ≥ 2` the fraction `4 / n` is a
sum of three positive unit fractions. -/
def ErdosStrausConjectureStmt : Prop := ∀ n : ℕ, 2 ≤ n → Solvable n

/-- Solvability propagates from a divisor to its multiples. -/
theorem solvable_of_dvd {d n : ℕ} (hd : d ∣ n) (hn : 0 < n) (h : Solvable d) : Solvable n := by
  obtain ⟨m, rfl⟩ := hd
  obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := h
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at hn
    · exact hm
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · simp at hn
    · exact hd0
  refine ⟨x * m, y * m, z * m, by positivity, by positivity, by positivity, ?_⟩
  have hxQ : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hyQ : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hzQ : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have key : (1 : ℚ) / (x * m) + 1 / (y * m) + 1 / (z * m)
      = ((1 : ℚ) / x + 1 / y + 1 / z) / m := by
    field_simp
  push_cast
  rw [key, ← hxyz, div_div]

/-- `4 / 2 = 1/1 + 1/2 + 1/2`. -/
theorem solvable_two : Solvable 2 :=
  ⟨1, 2, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `4 / 3 = 1/1 + 1/4 + 1/12`. -/
theorem solvable_three : Solvable 3 :=
  ⟨1, 4, 12, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Every even `n > 0` is solvable. -/
theorem solvable_of_even {n : ℕ} (hn : 0 < n) (h : n % 2 = 0) : Solvable n :=
  solvable_of_dvd (Nat.dvd_of_mod_eq_zero h) hn solvable_two

/-- Every positive multiple of `3` is solvable. -/
theorem solvable_of_three_dvd {n : ℕ} (hn : 0 < n) (h : n % 3 = 0) : Solvable n :=
  solvable_of_dvd (Nat.dvd_of_mod_eq_zero h) hn solvable_three

/-- If `n = 4k + 3` then `4/n = 1/(k+1) + 1/(2n(k+1)) + 1/(2n(k+1))`. -/
theorem solvable_of_mod_four_eq_three {n : ℕ} (h : n % 4 = 3) : Solvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
  refine ⟨k + 1, 2 * (4 * k + 3) * (k + 1), 2 * (4 * k + 3) * (k + 1),
    by positivity, by positivity, by positivity, ?_⟩
  have h1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have h2 : (4 * (k : ℚ) + 3) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- If `n = 3k + 2` then `4/n = 1/n + 1/(k+1) + 1/(n(k+1))`. -/
theorem solvable_of_mod_three_eq_two {n : ℕ} (h : n % 3 = 2) : Solvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 3 * k + 2 := ⟨n / 3, by omega⟩
  refine ⟨3 * k + 2, k + 1, (3 * k + 2) * (k + 1),
    by positivity, by positivity, by positivity, ?_⟩
  have h1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have h2 : (3 * (k : ℚ) + 2) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- If `n = 8k + 5` then `4/n = 1/(2k+2) + 1/(n(k+1)) + 1/(2n(k+1))`. -/
theorem solvable_of_mod_eight_eq_five {n : ℕ} (h : n % 8 = 5) : Solvable n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = 8 * k + 5 := ⟨n / 8, by omega⟩
  refine ⟨2 * k + 2, (8 * k + 5) * (k + 1), 2 * ((8 * k + 5) * (k + 1)),
    by positivity, by positivity, by positivity, ?_⟩
  have h1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have h2 : (8 * (k : ℚ) + 5) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **Partial result**: the Erdős–Straus conjecture holds for every `n ≥ 2` with
`n % 24 ≠ 1`. -/
theorem solvable_of_mod_24_ne_one {n : ℕ} (hn : 2 ≤ n) (h : n % 24 ≠ 1) : Solvable n := by
  have hn0 : 0 < n := by omega
  have hcases : n % 2 = 0 ∨ n % 3 = 0 ∨ n % 4 = 3 ∨ n % 3 = 2 ∨ n % 8 = 5 := by omega
  rcases hcases with h' | h' | h' | h' | h'
  · exact solvable_of_even hn0 h'
  · exact solvable_of_three_dvd hn0 h'
  · exact solvable_of_mod_four_eq_three h'
  · exact solvable_of_mod_three_eq_two h'
  · exact solvable_of_mod_eight_eq_five h'

/-- **Reduction to primes `≡ 1 (mod 24)`**: the full conjecture is equivalent to its
special case for primes congruent to `1` modulo `24`. -/
theorem ErdosStrausConjecture :
    ErdosStrausConjectureStmt ↔ ∀ p : ℕ, p.Prime → p % 24 = 1 → Solvable p := by
  constructor
  · intro h p hp _
    exact h p hp.two_le
  · intro h n hn
    have hn0 : 0 < n := by omega
    have hp : (n.minFac).Prime := Nat.minFac_prime (by omega)
    have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
    by_cases hmod : n.minFac % 24 = 1
    · exact solvable_of_dvd hdvd hn0 (h _ hp hmod)
    · exact solvable_of_dvd hdvd hn0 (solvable_of_mod_24_ne_one hp.two_le hmod)

end Brockian.ErdosStrausReduction
