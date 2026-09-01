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

def GiugaNumber (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ∣ (n / p - 1)

def OddGiugaExists : Prop := ∃ n : ℕ, Odd n ∧ GiugaNumber n

theorem not_giugaNumber_prime_pow {p k : ℕ} (hp : p.Prime) : ¬ GiugaNumber (p ^ k) := by
  rintro ⟨h1, h2, h3⟩
  match k with
  | 0 => simp at h1
  | 1 => exact h2 (by simpa using hp)
  | (m + 2) =>
    have hd : p ∣ p ^ (m + 2) := dvd_pow_self p (by omega)
    have hsub := h3 p hp hd
    rw [pow_succ, Nat.mul_div_cancel _ hp.pos] at hsub
    have h4 : p ∣ p ^ (m + 1) := dvd_pow_self p (by omega)
    have h5 : (1 : ℕ) ≤ p ^ (m + 1) := Nat.one_le_pow _ _ hp.pos
    have h6 : p ∣ p ^ (m + 1) - (p ^ (m + 1) - 1) := Nat.dvd_sub h4 hsub
    have h7 : p ^ (m + 1) - (p ^ (m + 1) - 1) = 1 := by omega
    rw [h7] at h6
    exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.mp h6)

