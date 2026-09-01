import Mathlib

def FortunateFor (P m : ℕ) : Prop :=
  1 < m ∧ (P + m).Prime ∧ ∀ k : ℕ, 1 < k → k < m → ¬ (P + k).Prime

def FortuneConjecture : Prop :=
  ∀ n P m : ℕ, P = primorial n → FortunateFor P m → m.Prime

/-- If `p` is a prime dividing the (positive) base `P`, then `p` cannot divide a
Fortunate number `m` for `P`: otherwise `p ∣ P + m`, forcing `P + m = p ≤ m`,
contradicting `0 < P`. -/
theorem fortunateFor_not_dvd_base_prime {P m p : ℕ} (hP : 0 < P) (h : FortunateFor P m)
    (hp : p.Prime) (hpP : p ∣ P) : ¬ p ∣ m := by
  obtain ⟨hm, hprime, -⟩ := h
  intro hpm
  have hdvd : p ∣ P + m := Nat.dvd_add hpP hpm
  have hpe : p = P + m := ((Nat.Prime.eq_one_or_self_of_dvd hprime p hdvd).resolve_left
    hp.ne_one)
  have hle : p ≤ m := Nat.le_of_dvd (by omega) hpm
  omega

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

