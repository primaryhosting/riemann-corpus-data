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

/-
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses a plain block comment `/- -/` rather than a module doc comment
-- `/-! -/`, because Lean 4 requires `import` to be preceded only by ordinary comments.)

import Mathlib

namespace Brockian
namespace RieselCovering

/-- A *Riesel number* is a positive odd natural number `k` such that `k * 2 ^ n - 1` is
composite for every `n ≥ 1`.  Compositeness is stated explicitly: there is a prime `p`
dividing `k * 2 ^ n - 1` which is strictly smaller than it. -/
def IsRieselNumber (k : ℕ) : Prop :=
  0 < k ∧ Odd k ∧ ∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, p.Prime ∧ p ∣ (k * 2 ^ n - 1) ∧ p < k * 2 ^ n - 1

/-- The modulus `11184810 = 2 * 3 * 5 * 7 * 13 * 17 * 241` of Riesel's congruence class. -/
lemma modulus_eq : (11184810 : ℕ) = 2 * 3 * 5 * 7 * 13 * 17 * 241 := by norm_num

/-- The covering system: for every residue `r` modulo `24` there is a prime in the covering
set `{3, 5, 7, 13, 17, 241}` for which `509203 * 2 ^ r ≡ 1`.  Moreover `2 ^ 24 ≡ 1` modulo
each of these primes. -/
lemma covering (r : ℕ) (hr : r < 24) :
    ∃ p ∈ [3, 5, 7, 13, 17, 241], (2 : ℕ) ^ 24 % p = 1 % p ∧ (509203 * 2 ^ r) % p = 1 % p := by
  interval_cases r <;> decide

/-- Each member of the covering set is prime and divides the modulus. -/
lemma covering_primes (p : ℕ) (hp : p ∈ [3, 5, 7, 13, 17, 241]) :
    p.Prime ∧ p ∣ 11184810 := by
  fin_cases hp <;> exact ⟨by norm_num, by norm_num⟩

/-- Key divisibility: if `p` divides the modulus, `2 ^ 24 ≡ 1 [MOD p]` and
`509203 * 2 ^ (n % 24) ≡ 1 [MOD p]`, then `p` divides `(509203 + 11184810 * m) * 2 ^ n - 1`. -/
lemma dvd_of_covering (m n p : ℕ) (hp : p ∣ 11184810) (h24 : (2 : ℕ) ^ 24 ≡ 1 [MOD p])
    (hr : 509203 * 2 ^ (n % 24) ≡ 1 [MOD p]) :
    p ∣ (509203 + 11184810 * m) * 2 ^ n - 1 := by
  have hzero : 11184810 * m ≡ 0 [MOD p] := (Nat.modEq_zero_iff_dvd).mpr (hp.mul_right m)
  have hK : (509203 + 11184810 * m) ≡ 509203 [MOD p] := by
    calc 509203 + 11184810 * m ≡ 509203 + 0 [MOD p] := Nat.ModEq.add_left _ hzero
      _ = 509203 := by ring
  have hpow : (2 : ℕ) ^ n ≡ 2 ^ (n % 24) [MOD p] := by
    conv_lhs => rw [← Nat.div_add_mod n 24]
    rw [pow_add, pow_mul]
    calc ((2 : ℕ) ^ 24) ^ (n / 24) * 2 ^ (n % 24)
        ≡ 1 ^ (n / 24) * 2 ^ (n % 24) [MOD p] := Nat.ModEq.mul_right _ (h24.pow _)
      _ = 2 ^ (n % 24) := by ring
  have h1 : (509203 + 11184810 * m) * 2 ^ n ≡ 1 [MOD p] := (hK.mul hpow).trans hr
  have hle : 1 ≤ (509203 + 11184810 * m) * 2 ^ n := Nat.one_le_iff_ne_zero.mpr (by positivity)
  exact (Nat.modEq_iff_dvd' hle).mp h1.symm

/-- Every member of Riesel's congruence class `509203 + 11184810 * m` is a Riesel number. -/
theorem isRieselNumber_riesel_class (m : ℕ) : IsRieselNumber (509203 + 11184810 * m) := by
  refine ⟨by positivity, ⟨254601 + 5592405 * m, by ring⟩, ?_⟩
  intro n hn
  obtain ⟨p, hpmem, h24, hr⟩ := covering (n % 24) (Nat.mod_lt _ (by norm_num))
  obtain ⟨hprime, hpdvd⟩ := covering_primes p hpmem
  refine ⟨p, hprime, dvd_of_covering m n p hpdvd h24 hr, ?_⟩
  have hple : p ≤ 241 := by fin_cases hpmem <;> norm_num
  have h2 : (2 : ℕ) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hbig : 509203 * 2 ≤ (509203 + 11184810 * m) * 2 ^ n := by
    calc 509203 * 2 = 509203 * 2 ^ 1 := by norm_num
      _ ≤ (509203 + 11184810 * m) * 2 ^ n := Nat.mul_le_mul (Nat.le_add_right _ _) h2
  omega

/-- **The Riesel problem (Riesel's theorem).**  There are infinitely many Riesel numbers, i.e.
odd `k > 0` for which `k * 2 ^ n - 1` is composite for all `n ≥ 1`.  The proof uses Riesel's
covering system with the primes `{3, 5, 7, 13, 17, 241}` and the congruence class
`k ≡ 509203 (mod 11184810)`. -/
theorem RieselProblem : {k : ℕ | IsRieselNumber k}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun m : ℕ => 509203 + 11184810 * m)
  · intro a b hab
    simpa using hab
  · intro m
    exact isRieselNumber_riesel_class m

/-- Consequence: if `k` is a Riesel number then `k * 2 ^ n - 1` is never prime for `n ≥ 1`. -/
theorem not_prime_of_isRieselNumber {k : ℕ} (hk : IsRieselNumber k) (n : ℕ) (hn : 1 ≤ n) :
    ¬ (k * 2 ^ n - 1).Prime := by
  obtain ⟨p, hp, hdvd, hlt⟩ := hk.2.2 n hn
  intro hprime
  rcases hprime.eq_one_or_self_of_dvd p hdvd with h | h
  · exact hp.one_lt.ne' h
  · omega

end RieselCovering
end Brockian

