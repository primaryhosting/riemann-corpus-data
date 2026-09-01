/-
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option autoImplicit false

namespace Brockian

/-- The list of all primes below the wheel modulus `1153`. -/
def wheelPrimes1153 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
   101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
   197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307,
   311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421,
   431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547,
   557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
   661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797,
   809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929,
   937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039,
   1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151]

set_option maxRecDepth 100000 in
/-- Every entry of `wheelPrimes1153` is indeed prime. -/
theorem prime_of_mem_wheelPrimes1153 : ∀ p ∈ wheelPrimes1153, Nat.Prime p := by
  intro p hp
  fin_cases hp <;> norm_num

set_option maxRecDepth 100000 in
/-- The exhaustive finite search: for every `k < 575`, the even number `2 * k + 4` splits as a
sum of two entries of `wheelPrimes1153`. -/
theorem wheelPrimes1153_split :
    ∀ k ∈ List.range 575, ∃ p ∈ wheelPrimes1153, (2 * k + 4 - p) ∈ wheelPrimes1153 := by
  decide +kernel

/-- **Goldbach wheel, `K = 2`, modulus `1153`.**
Every even natural number `n` with `4 ≤ n ≤ 1153` is a sum of two primes. -/
theorem GoldbachWheelK2_1153 (n : ℕ) (h4 : 4 ≤ n) (hn : n ≤ 1153) (heven : Even n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  obtain ⟨m, rfl⟩ := heven
  have hk : m - 2 ∈ List.range 575 := by
    rw [List.mem_range]; omega
  obtain ⟨p, hp, hq⟩ := wheelPrimes1153_split (m - 2) hk
  have h2 : 2 * (m - 2) + 4 = m + m := by omega
  rw [h2] at hq
  have hq2 := prime_of_mem_wheelPrimes1153 _ hq
  refine ⟨p, m + m - p, prime_of_mem_wheelPrimes1153 p hp, hq2, ?_⟩
  have := hq2.two_le
  omega

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

