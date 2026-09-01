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

import Mathlib

/-!
# Odd Giuga Exists
Category: Brockian Conjecture
Target: Brockian.GiugaNumbers.OddGiugaExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian.GiugaNumbers

/-- A *Giuga number* is a composite natural number `n > 1` such that for every prime `p`
dividing `n` we have `p ∣ n / p - 1`.  The smallest Giuga number is `30`. -/
def IsGiuga (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ∣ (n / p - 1)

/-- A finite set `S` of primes, of size at least `2`, such that for each `p ∈ S` the product of
the *other* elements of `S` is `≡ 1 mod p`.  These are exactly the prime-factor sets of Giuga
numbers. -/
def IsGiugaSet (S : Finset ℕ) : Prop :=
  2 ≤ S.card ∧ (∀ p ∈ S, p.Prime) ∧ ∀ p ∈ S, p ∣ (∏ q ∈ S.erase p, q) - 1

theorem isGiuga_thirty : IsGiuga 30 := by
  refine ⟨by norm_num, by decide, ?_⟩
  intro p _ hpd
  have hp30 : p ≤ 30 := Nat.le_of_dvd (by norm_num) hpd
  interval_cases p <;> revert hpd <;> decide

/-- Every Giuga number is squarefree. -/
theorem squarefree_of_isGiuga {n : ℕ} (h : IsGiuga n) : Squarefree n := by
  obtain ⟨hn1, _, hdvd⟩ := h
  rw [Nat.squarefree_iff_prime_squarefree]
  rintro p hp ⟨k, hk⟩
  have hpn : p ∣ n := ⟨p * k, by rw [hk]; ring⟩
  have hnp : n / p = p * k := by
    rw [hk]; rw [show p * p * k = p * (p * k) by ring, Nat.mul_div_cancel_left _ hp.pos]
  have h1 : p ∣ n / p := ⟨k, hnp⟩
  have h2 : p ∣ n / p - 1 := hdvd p hp hpn
  have hpos : 1 ≤ n / p := Nat.one_le_div_iff hp.pos |>.2 (Nat.le_of_dvd (by omega) hpn)
  have h3 : p ∣ n / p - (n / p - 1) := Nat.dvd_sub' h1 h2
  rw [show n / p - (n / p - 1) = 1 by omega] at h3
  exact absurd (Nat.le_of_dvd one_pos h3) (by have := hp.two_le; omega)

end Brockian.GiugaNumbers

