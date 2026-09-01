import Mathlib

/-- `n` has the Lehmer property: `φ n` divides `n - 1`. -/
def LehmerProperty (n : ℕ) : Prop := Nat.totient n ∣ n - 1

/-- Lehmer's totient problem (**OPEN**), recorded as an unproven `def`:
only primes have the Lehmer property (above 1). -/
def LehmerTotientConjecture : Prop :=
  ∀ n : ℕ, 1 < n → LehmerProperty n → Nat.Prime n

/-- Any Lehmer number is squarefree: if `p ^ 2 ∣ n` then `p ∣ φ n ∣ n - 1`,
while also `p ∣ n`, forcing `p ∣ 1`. -/
theorem squarefree_of_lehmerProperty {n : ℕ} (hn : 1 < n)
    (h : LehmerProperty n) : Squarefree n := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hdvd
  obtain ⟨m, hm⟩ := hdvd
  have hpk : p ∣ p * m := Dvd.intro m rfl
  have hphi : p ∣ Nat.totient n := by
    rw [hm, mul_assoc, Nat.totient_mul_of_prime_of_dvd hp hpk]
    exact Dvd.intro _ rfl
  have h1 : p ∣ n - 1 := hphi.trans h
  have h2 : p ∣ n := ⟨p * m, by rw [hm]; ring⟩
  have hone : p ∣ 1 := by
    have := Nat.dvd_sub h2 h1
    simpa [Nat.sub_sub_self hn.le] using this
  exact hp.one_lt.ne' (Nat.dvd_one.mp hone)

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

