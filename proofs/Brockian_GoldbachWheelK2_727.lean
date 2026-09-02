/-
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Brockian

/-- The `K = 2` Goldbach wheel property for a modulus `m`: every even number `n`
with `4 ≤ n ≤ m` is a sum of two primes. -/
def GoldbachWheelK2 (m : ℕ) : Prop :=
  ∀ n : ℕ, 4 ≤ n → n ≤ m → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

/-- The list of all primes below the wheel modulus `727` (inclusive). -/
def wheelPrimes727 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
   97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
   193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293,
   307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419,
   421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541,
   547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653,
   659, 661, 673, 677, 683, 691, 701, 709, 719, 727]

/-- Every entry of `wheelPrimes727` is indeed prime. -/
lemma wheelPrimes727_prime : ∀ p ∈ wheelPrimes727, Nat.Prime p := by
  decide

/-- Each even `n` with `4 ≤ n ≤ 727` splits as a sum of two entries of `wheelPrimes727`. -/
lemma wheelPrimes727_covers :
    ∀ n ∈ Finset.Icc 4 727, Even n → ∃ p ∈ wheelPrimes727, ∃ q ∈ wheelPrimes727, p + q = n := by
  decide

/-- **Goldbach wheel, `K = 2`, modulus `727`.**  Every even `n` with `4 ≤ n ≤ 727`
is the sum of two primes. -/
theorem GoldbachWheelK2_727 : GoldbachWheelK2 727 := by
  intro n h4 hle hn
  obtain ⟨p, hp, q, hq, hpq⟩ := wheelPrimes727_covers n (Finset.mem_Icc.mpr ⟨h4, hle⟩) hn
  exact ⟨p, q, wheelPrimes727_prime p hp, wheelPrimes727_prime q hq, hpq⟩

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

