import Mathlib

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


set_option maxRecDepth 100000

namespace Brockian

/-- The "spokes" of the wheel: the small primes that are used as the smaller summand
in the Goldbach decompositions below.  (For every even `n ≤ 1051` one of these works.) -/
def wheelSpokes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]

/-- A kernel-friendly primality certificate: trial division by all `m < 40` with `m * m ≤ p`.
It is sound for every `p < 1600`. -/
def isPrimeCert (p : ℕ) : Bool :=
  decide (2 ≤ p) && ((List.range 40).all fun m => !(decide (2 ≤ m) && decide (m * m ≤ p) && (p % m == 0)))

theorem prime_of_isPrimeCert {p : ℕ} (hb : p < 1600) (h : isPrimeCert p = true) : Nat.Prime p := by
  rw [isPrimeCert, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h2, hall⟩ := h
  have h2' : 2 ≤ p := by simpa using h2
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h2', ?_⟩
  intro m hm2 hms hdvd
  have hmm : m * m ≤ p := Nat.le_sqrt.mp hms
  have hm40 : m < 40 := by nlinarith
  have hcontra := hall m (List.mem_range.mpr hm40)
  simp only [Bool.not_eq_true', Bool.and_eq_false_imp, decide_eq_true_eq, beq_iff_eq,
    Bool.not_eq_eq_eq_not, Bool.not_true] at hcontra
  have : p % m = 0 := Nat.eq_zero_of_dvd_of_lt hdvd |> fun _ => (Nat.mod_eq_zero_of_dvd hdvd)
  simp [hm2, hmm, this] at hcontra

/-- The finite Goldbach verification for the wheel of modulus `1051`: every even `n` with
`4 ≤ n < 1052` is the sum of a spoke prime and another prime. -/
def goldbachCheck (N : ℕ) : Bool :=
  (List.range N).all fun n =>
    !(decide (4 ≤ n) && (n % 2 == 0)) || wheelSpokes.any (fun p => isPrimeCert p && isPrimeCert (n - p))

theorem goldbachCheck_1052 : goldbachCheck 1052 = true := by decide +kernel

/-- **Goldbach wheel, K = 2, modulus 1051.**
Every even natural number `n` with `4 ≤ n ≤ 1051` is a sum of two primes. -/
theorem GoldbachWheelK2_1051 :
    ∀ n : ℕ, 4 ≤ n → n ≤ 1051 → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  intro n h4 hle hev
  have hchk := goldbachCheck_1052
  rw [goldbachCheck, List.all_eq_true] at hchk
  have hn := hchk n (List.mem_range.mpr (by omega))
  have hmod : n % 2 = 0 := Nat.even_iff.mp hev
  simp only [h4, hmod, decide_true, Bool.and_self, beq_self_eq_true, Bool.not_true,
    Bool.false_or, decide_eq_true_eq, Bool.and_true, List.any_eq_true] at hn
  obtain ⟨p, hp_mem, hp⟩ := hn
  rw [Bool.and_eq_true] at hp
  have hspoke : ∀ p ∈ wheelSpokes, p < 1600 := by decide
  have hp_prime : Nat.Prime p := prime_of_isPrimeCert (hspoke p hp_mem) hp.1
  have hq_prime : Nat.Prime (n - p) := prime_of_isPrimeCert (by omega) hp.2
  have hpn : p ≤ n := by have := hq_prime.two_le; omega
  exact ⟨p, n - p, hp_prime, hq_prime, by omega⟩

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

