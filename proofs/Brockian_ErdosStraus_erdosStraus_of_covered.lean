/-
  Brockian/ErdosStraus.lean — unconditional partial results toward the
  Erdős–Straus conjecture (OPEN since 1948).

  The Erdős–Straus conjecture asserts that for every integer `n ≥ 2` the
  equation `4/n = 1/x + 1/y + 1/z` has a solution in positive integers.
  It is UNSOLVED. This file proves genuine, unconditional PARTIAL results:

    • an explicit decomposition for every even `n`;
    • an explicit decomposition for every `n` divisible by 3;
    • the key structural fact that the property is inherited by multiples,
      hence the whole conjecture reduces to the case of prime `n`;
    • explicit decompositions for the residue classes `n ≡ 3 (mod 4)` and
      `n ≡ 2 (mod 3)`.

  The full conjecture is recorded honestly as a `def` (`ErdosStrausConjecture`)
  and is deliberately NOT proved: what remains genuinely open is the prime
  case in the hard residue classes (famously `p ≡ 1, 121, 169, 289, 361, 529`
  mod 840).

  Verified @ lean-4.32.0 (Mathlib). No sorry / admit / native_decide / added axiom.
-/
import Mathlib

namespace Brockian.ErdosStraus

/-- `n` admits an Erdős–Straus decomposition: `4/n` is a sum of three positive
unit fractions. Worked over `ℚ` with `x, y, z` cast from `ℕ`. -/
def ErdosStraus (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧
    (4 : ℚ) / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ)

/-! ### Explicit families -/

/-- **Even case.** Every even `n ≥ 2` has an Erdős–Straus decomposition.
With `n = 2m` the witnesses are `x = m`, `y = m+1`, `z = m(m+1)`, using the
identity `1/m + 1/(m+1) + 1/(m(m+1)) = 2/m = 4/(2m)`. -/
theorem erdosStraus_even {n : ℕ} (hn : 0 < n) (he : 2 ∣ n) : ErdosStraus n := by
  obtain ⟨m, hm⟩ := he
  have hmpos : 0 < m := by omega
  refine ⟨m, m + 1, m * (m + 1), hmpos, by omega, Nat.mul_pos hmpos (by omega), ?_⟩
  have hmc : (m : ℚ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hm1 : (m : ℚ) + 1 ≠ 0 := ne_of_gt (by positivity)
  have hncast : (n : ℚ) = 2 * (m : ℚ) := by exact_mod_cast hm
  push_cast
  rw [hncast]
  field_simp
  ring

/-- **Divisible-by-three case.** Every `n ≥ 2` with `3 ∣ n` has an Erdős–Straus
decomposition. With `n = 3m` the witnesses are `x = m`, `y = 3m+1`,
`z = 3m(3m+1)`, using `1/m + 1/(3m+1) + 1/(3m(3m+1)) = 4/(3m)`. -/
theorem erdosStraus_dvd_three {n : ℕ} (hn : 0 < n) (h3 : 3 ∣ n) : ErdosStraus n := by
  obtain ⟨m, hm⟩ := h3
  have hmpos : 0 < m := by omega
  refine ⟨m, 3 * m + 1, 3 * m * (3 * m + 1), hmpos, by omega,
    Nat.mul_pos (by omega) (by omega), ?_⟩
  have hmc : (m : ℚ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have h1 : 3 * (m : ℚ) + 1 ≠ 0 := ne_of_gt (by positivity)
  have hncast : (n : ℚ) = 3 * (m : ℚ) := by exact_mod_cast hm
  push_cast
  rw [hncast]
  field_simp
  ring

/-! ### The key reduction: multiplicativity -/

/-- **Inheritance by multiples (the structural core).** If a divisor `d` of `n`
admits an Erdős–Straus decomposition, then so does `n`. Writing `n = d·t` and
`4/d = 1/x + 1/y + 1/z`, the decomposition scales termwise:
`4/n = (1/t)(4/d) = 1/(t x) + 1/(t y) + 1/(t z)`. -/
theorem erdosStraus_of_dvd {d n : ℕ} (hd : ErdosStraus d) (hdn : d ∣ n) (hn : 0 < n) :
    ErdosStraus n := by
  obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := hd
  obtain ⟨t, ht⟩ := hdn
  have htpos : 0 < t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · rw [h, Nat.mul_zero] at ht; omega
    · exact h
  refine ⟨t * x, t * y, t * z, Nat.mul_pos htpos hx, Nat.mul_pos htpos hy,
    Nat.mul_pos htpos hz, ?_⟩
  have htc : (t : ℚ) ≠ 0 := by exact_mod_cast htpos.ne'
  have hxc : (x : ℚ) ≠ 0 := by exact_mod_cast hx.ne'
  have hyc : (y : ℚ) ≠ 0 := by exact_mod_cast hy.ne'
  have hzc : (z : ℚ) ≠ 0 := by exact_mod_cast hz.ne'
  have hncast : (n : ℚ) = (d : ℚ) * (t : ℚ) := by exact_mod_cast ht
  push_cast
  rw [hncast, div_mul_eq_div_div, hxyz]
  field_simp

/-- **Reduction to the primes.** If every prime satisfies Erdős–Straus, then so
does every `n ≥ 2`: pick any prime factor `p` of `n` and scale up via
`erdosStraus_of_dvd`. This isolates the genuine open content in the prime case. -/
theorem erdosStraus_of_prime_case (H : ∀ p : ℕ, p.Prime → ErdosStraus p) {n : ℕ}
    (hn : 2 ≤ n) : ErdosStraus n := by
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
  exact erdosStraus_of_dvd (H p hp) hpn (by omega)

/-! ### Odd residue classes -/

/-- **Class `n ≡ 3 (mod 4)`.** With `n + 1 = 4t` (so `n = 4t - 1`), the witnesses
are `x = t+1`, `y = t(t+1)`, `z = t·n`, using
`1/(t+1) + 1/(t(t+1)) + 1/(t(4t-1)) = 1/t + 1/(t(4t-1)) = 4/(4t-1)`.
This closes the residues `7, 11, 19, 23 (mod 24)` among `n` coprime to 6. -/
theorem erdosStraus_mod4_three {n : ℕ} (hn : 0 < n) (h : n % 4 = 3) : ErdosStraus n := by
  obtain ⟨t, ht⟩ : ∃ t, n + 1 = 4 * t := ⟨(n + 1) / 4, by omega⟩
  have htpos : 0 < t := by omega
  refine ⟨t + 1, t * (t + 1), t * n, by omega, Nat.mul_pos htpos (by omega),
    Nat.mul_pos htpos hn, ?_⟩
  have htc : (t : ℚ) ≠ 0 := by exact_mod_cast htpos.ne'
  have ht1 : (t : ℚ) + 1 ≠ 0 := ne_of_gt (by positivity)
  have htge : (1 : ℚ) ≤ (t : ℚ) := by exact_mod_cast htpos
  have hncast : (n : ℚ) = 4 * (t : ℚ) - 1 := by
    have h4 : (n : ℚ) + 1 = 4 * (t : ℚ) := by exact_mod_cast ht
    linarith
  have hpos : (0 : ℚ) < 4 * (t : ℚ) - 1 := by linarith
  have h4t1 : 4 * (t : ℚ) - 1 ≠ 0 := ne_of_gt hpos
  push_cast
  rw [hncast]
  field_simp
  ring

/-- **Class `n ≡ 2 (mod 3)`.** With `n + 1 = 3j` (so `n = 3j - 1`), the witnesses
are `x = j`, `y = n`, `z = j·n`, using the identity
`1/j + 1/n + 1/(jn) = (n + j + 1)/(jn) = 4j/(jn) = 4/n` since `n = 3j - 1`.
This closes the residues `5, 11, 17, 23 (mod 24)` among `n` coprime to 6. -/
theorem erdosStraus_mod3_two {n : ℕ} (hn : 0 < n) (h : n % 3 = 2) : ErdosStraus n := by
  obtain ⟨j, hj⟩ : ∃ j, n + 1 = 3 * j := ⟨(n + 1) / 3, by omega⟩
  have hjpos : 0 < j := by omega
  refine ⟨j, n, j * n, hjpos, hn, Nat.mul_pos hjpos hn, ?_⟩
  have hjc : (j : ℚ) ≠ 0 := by exact_mod_cast hjpos.ne'
  have hjge : (1 : ℚ) ≤ (j : ℚ) := by exact_mod_cast hjpos
  have hncast : (n : ℚ) = 3 * (j : ℚ) - 1 := by
    have h3 : (n : ℚ) + 1 = 3 * (j : ℚ) := by exact_mod_cast hj
    linarith
  have hpos : (0 : ℚ) < 3 * (j : ℚ) - 1 := by linarith
  have h3j1 : 3 * (j : ℚ) - 1 ≠ 0 := ne_of_gt hpos
  push_cast
  rw [hncast]
  field_simp
  ring

/-- **Consolidated coverage.** Every `n ≥ 1` that is even, divisible by 3,
`≡ 3 (mod 4)`, or `≡ 2 (mod 3)` admits an Erdős–Straus decomposition —
unconditionally. Among `n` coprime to 6 this leaves only `n ≡ 1, 13 (mod 24)`
(the classes feeding the hard prime residues). -/
theorem erdosStraus_of_covered {n : ℕ} (hn : 0 < n)
    (hcov : 2 ∣ n ∨ 3 ∣ n ∨ n % 4 = 3 ∨ n % 3 = 2) : ErdosStraus n := by
  rcases hcov with h | h | h | h
  · exact erdosStraus_even hn h
  · exact erdosStraus_dvd_three hn h
  · exact erdosStraus_mod4_three hn h
  · exact erdosStraus_mod3_two hn h

/-! ### The honest frontier -/

/-- **The Erdős–Straus conjecture (OPEN).** Stated, not proved. The results above
resolve all `n` divisible by 2 or 3, and the residue classes `n ≡ 3 (mod 4)` and
`n ≡ 2 (mod 3)`, and reduce the remainder to prime `n` (`erdosStraus_of_prime_case`).
What remains genuinely open is the conjecture for primes in the hard residue
classes (famously `p ≡ 1, 121, 169, 289, 361, 529` mod 840). This `def` records
the statement; it is deliberately NOT a theorem. -/
def ErdosStrausConjecture : Prop := ∀ n : ℕ, 2 ≤ n → ErdosStraus n

end Brockian.ErdosStraus
