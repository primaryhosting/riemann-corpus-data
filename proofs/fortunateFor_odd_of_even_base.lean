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

def FortunateFor (P m : ℕ) : Prop :=
  1 < m ∧ (P + m).Prime ∧ ∀ k : ℕ, 1 < k → k < m → ¬ (P + k).Prime

def FortuneConjecture : Prop :=
  ∀ n P m : ℕ, P = primorial n → FortunateFor P m → m.Prime

/-- For an even base `P > 0`, any Fortunate number `m` for `P` is odd:
`P + m ≥ 4` is prime, hence odd, and `P` is even, so `m` is odd. -/
theorem fortunateFor_odd_of_even_base {P m : ℕ} (hP : 0 < P) (hE : Even P)
    (h : FortunateFor P m) : Odd m := by
  obtain ⟨hm, hp, -⟩ := h
  obtain ⟨t, ht⟩ := hE
  have hodd : Odd (P + m) := hp.odd_of_ne_two (by omega)
  obtain ⟨s, hs⟩ := hodd
  exact ⟨s - t, by omega⟩

