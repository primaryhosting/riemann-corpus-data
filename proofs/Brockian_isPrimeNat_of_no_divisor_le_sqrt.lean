/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: the required header above is a module doc comment, and Lean 4 forbids any
`import` after it, so this file is written in pure core Lean (no Mathlib) and is fully
self-contained.  The file `RequestProject/GoldbachWheelK2_1153Mathlib.lean` imports Mathlib and
this file, proves `Brockian.IsPrimeNat n ↔ Nat.Prime n`, and restates the result in Mathlib
vocabulary.
-/

namespace Brockian

/-- A natural number is prime when it is at least `2` and its only divisors are `1` and itself. -/
def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ m : Nat, m ∣ n → m = 1 ∨ m = n

/-- Trial-division criterion: a number `n ≥ 2` with no divisor `m` satisfying `m * m ≤ n`
(other than `1`) is prime. -/
theorem isPrimeNat_of_no_divisor_le_sqrt {n : Nat} (h2 : 2 ≤ n)
    (H : ∀ m : Nat, 2 ≤ m → m * m ≤ n → ¬ m ∣ n) : IsPrimeNat n := by
  refine ⟨h2, ?_⟩
  intro m hm
  cases hm with
  | intro k hk =>
    have hm0 : m ≠ 0 := by
      intro h; subst h; simp at hk; omega
    have hk0 : k ≠ 0 := by
      intro h; subst h; simp at hk; omega
    rcases Nat.lt_or_ge m 2 with hlt | hm2
    · exact Or.inl (by omega)
    · rcases Nat.lt_or_ge k 2 with hklt | hk2
      · have hk1 : k = 1 := by omega
        subst hk1
        exact Or.inr (by omega)
      · exfalso
        rcases Nat.le_total m k with h | h
        · exact H m hm2 (by
            calc m * m ≤ m * k := Nat.mul_le_mul_left m h
              _ = n := hk.symm) ⟨k, hk⟩
        · exact H k hk2 (by
            calc k * k ≤ m * k := Nat.mul_le_mul_right k h
              _ = n := hk.symm) ⟨m, by rw [hk, Nat.mul_comm]⟩

/-- The wheel modulus `1153` is prime. -/
theorem isPrimeNat_1153 : IsPrimeNat 1153 := by
  refine isPrimeNat_of_no_divisor_le_sqrt (by omega) ?_
  have key : ∀ m : Nat, m < 34 → 2 ≤ m → ¬ m ∣ 1153 := by decide
  intro m hm2 hsq
  refine key m ?_ hm2
  rcases Nat.lt_or_ge m 34 with h | h
  · exact h
  · have : 34 * 34 ≤ m * m := Nat.mul_le_mul h h
    omega

theorem isPrimeNat_13 : IsPrimeNat 13 := by
  refine isPrimeNat_of_no_divisor_le_sqrt (by omega) ?_
  have key : ∀ m : Nat, m < 4 → 2 ≤ m → ¬ m ∣ 13 := by decide
  intro m hm2 hsq
  refine key m ?_ hm2
  rcases Nat.lt_or_ge m 4 with h | h
  · exact h
  · have : 4 * 4 ≤ m * m := Nat.mul_le_mul h h
    omega

theorem isPrimeNat_2293 : IsPrimeNat 2293 := by
  refine isPrimeNat_of_no_divisor_le_sqrt (by omega) ?_
  have key : ∀ m : Nat, m < 48 → 2 ≤ m → ¬ m ∣ 2293 := by decide
  intro m hm2 hsq
  refine key m ?_ hm2
  rcases Nat.lt_or_ge m 48 with h | h
  · exact h
  · have : 48 * 48 ≤ m * m := Nat.mul_le_mul h h
    omega

/--
**Goldbach wheel, `K = 2`, new wheel modulus `1153`.**

The wheel modulus `1153` is prime, and the associated even number `2 * 1153 = 2306` has a
Goldbach representation as a sum of `K = 2` primes, each of which is a unit of the wheel,
i.e. not divisible by the modulus `1153`.

Witnesses: `2306 = 13 + 2293`, with `13` and `2293` prime.
-/
theorem GoldbachWheelK2_1153 :
    IsPrimeNat 1153 ∧
      ∃ p q : Nat, IsPrimeNat p ∧ IsPrimeNat q ∧ p + q = 2 * 1153 ∧
        p % 1153 ≠ 0 ∧ q % 1153 ≠ 0 :=
  ⟨isPrimeNat_1153, 13, 2293, isPrimeNat_13, isPrimeNat_2293, by decide, by decide, by decide⟩

end Brockian

import Mathlib
import RequestProject.GoldbachWheelK2_1153

/-!
# Goldbach Wheel K 2 1153 — Mathlib restatement

`RequestProject/GoldbachWheelK2_1153.lean` must be import-free (its mandated header is a module
doc comment, after which Lean forbids `import`), so it uses its own primality predicate
`Brockian.IsPrimeNat`.  Here we identify that predicate with Mathlib's `Nat.Prime` and restate
the Goldbach wheel result in Mathlib vocabulary.
-/

namespace Brockian

/-- The self-contained primality predicate agrees with Mathlib's `Nat.Prime`. -/
theorem isPrimeNat_iff_prime {n : ℕ} : IsPrimeNat n ↔ Nat.Prime n := by
  constructor
  · rintro ⟨h2, hdvd⟩
    refine Nat.prime_def.mpr ⟨h2, fun m hm => ?_⟩
    rcases hdvd m hm with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro hp
    exact ⟨hp.two_le, fun m hm => (Nat.Prime.eq_one_or_self_of_dvd hp m hm)⟩

/-- Mathlib-phrased form of `Brockian.GoldbachWheelK2_1153`: the wheel modulus `1153` is prime
and `2 * 1153` is a sum of two primes, both coprime to the modulus. -/
theorem goldbachWheelK2_1153_prime :
    Nat.Prime 1153 ∧
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2 * 1153 ∧
        Nat.Coprime p 1153 ∧ Nat.Coprime q 1153 := by
  obtain ⟨h1153, p, q, hp, hq, hsum, hpm, hqm⟩ := GoldbachWheelK2_1153
  have hP : Nat.Prime 1153 := isPrimeNat_iff_prime.mp h1153
  refine ⟨hP, p, q, isPrimeNat_iff_prime.mp hp, isPrimeNat_iff_prime.mp hq, hsum, ?_, ?_⟩
  · exact (Nat.Prime.coprime_iff_not_dvd hP).mpr
      (fun h => hpm (Nat.dvd_iff_mod_eq_zero.mp h)) |>.symm
  · exact (Nat.Prime.coprime_iff_not_dvd hP).mpr
      (fun h => hqm (Nat.dvd_iff_mod_eq_zero.mp h)) |>.symm

end Brockian

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

