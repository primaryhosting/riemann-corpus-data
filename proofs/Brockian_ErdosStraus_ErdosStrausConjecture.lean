import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.ErdosStraus

/-- `ErdosStraus n` says that `4 / n` can be written as a sum of three unit fractions
with positive natural denominators. -/
def ErdosStraus (n : ℕ) : Prop :=
  ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ (4 : ℚ) / n = 1 / x + 1 / y + 1 / z

/-- If `4/m` is a sum of three unit fractions, so is `4/(m*k)` for any `k > 0`. -/
theorem ErdosStraus.mul_right {m : ℕ} (hm : ErdosStraus m) {k : ℕ} (hk : 0 < k) :
    ErdosStraus (m * k) := by
  obtain ⟨x, y, z, hx, hy, hz, h⟩ := hm
  refine ⟨x * k, y * k, z * k, by positivity, by positivity, by positivity, ?_⟩
  have hkQ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hxQ : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hyQ : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hzQ : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have hsplit : (4 : ℚ) / ((m : ℚ) * (k : ℚ)) = (1 / k) * (4 / m) := by
    rw [div_mul_div_comm]
    ring_nf
  rw [Nat.cast_mul, hsplit, h]
  push_cast
  field_simp
  ring

/-- The case `n = 2`: `4/2 = 1/1 + 1/2 + 1/2`. -/
theorem erdosStraus_two : ErdosStraus 2 :=
  ⟨1, 2, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Every even `n ≥ 2` satisfies the Erdős–Straus property. -/
theorem erdosStraus_of_even {n : ℕ} (hn : 2 ≤ n) (h2 : 2 ∣ n) : ErdosStraus n := by
  obtain ⟨k, rfl⟩ := h2
  have hk : 0 < k := by omega
  exact erdosStraus_two.mul_right hk

/-- Every `n ≡ 3 [MOD 4]` satisfies the Erdős–Straus property:
with `n = 4k+3`, `x = k+1` and `m = n*(k+1)` we have `4/n = 1/x + 1/m`, and
`1/m = 1/(m+1) + 1/(m*(m+1))`. -/
theorem erdosStraus_of_mod_four_eq_three {n : ℕ} (h : n % 4 = 3) : ErdosStraus n := by
  obtain ⟨k, hk⟩ : ∃ k, n = 4 * k + 3 := ⟨n / 4, by omega⟩
  subst hk
  set N : ℕ := 4 * k + 3 with hN
  set m : ℕ := N * (k + 1) with hm
  have hmpos : 0 < m := by
    have : 0 < N := by omega
    positivity
  refine ⟨k + 1, m + 1, m * (m + 1), by omega, by omega, by positivity, ?_⟩
  have hNQ : (N : ℚ) ≠ 0 := by
    have hNpos : (0 : ℕ) < N := by omega
    exact Nat.cast_ne_zero.mpr hNpos.ne'
  have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hmpos.ne'
  have hm1Q : ((m : ℚ) + 1) ≠ 0 := by positivity
  have hkQ : ((k : ℚ) + 1) ≠ 0 := by positivity
  have step : (1 : ℚ) / ((m : ℚ) + 1) + 1 / ((m : ℚ) * ((m : ℚ) + 1)) = 1 / (m : ℚ) := by
    field_simp
    ring
  have hmval : (m : ℚ) = (N : ℚ) * ((k : ℚ) + 1) := by
    rw [hm]; push_cast; ring
  push_cast
  rw [show ((m : ℚ) * ((m : ℚ) + 1)) = ((m : ℚ) * ((m : ℚ) + 1)) from rfl, step, hmval]
  rw [hN]
  push_cast
  field_simp
  ring

/-- **Reduction of the Erdős–Straus conjecture to primes `p ≡ 1 [MOD 4]`.**
If `4/p` is a sum of three unit fractions for every prime `p ≡ 1 mod 4`, then
`4/n` is a sum of three unit fractions for every `n ≥ 2`. -/
theorem ErdosStrausConjecture
    (hprime : ∀ p : ℕ, p.Prime → p % 4 = 1 → ErdosStraus p) :
    ∀ n : ℕ, 2 ≤ n → ErdosStraus n := by
  intro n hn
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (n := n) (by omega)
  obtain ⟨k, rfl⟩ := hpd
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rw [Nat.mul_zero] at hn; omega
    · exact h
  have hp' : ErdosStraus p := by
    have hcases : p % 4 = 0 ∨ p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3 := by omega
    rcases hcases with h | h | h | h
    · exact erdosStraus_of_even hp.two_le (by omega)
    · exact hprime p hp h
    · exact erdosStraus_of_even hp.two_le (by omega)
    · exact erdosStraus_of_mod_four_eq_three h
  exact hp'.mul_right hkpos

end Brockian.ErdosStraus

