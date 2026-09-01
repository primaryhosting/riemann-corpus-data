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

theorem fortunateFor_unique {P m m' : ℕ} (h : FortunateFor P m) (h' : FortunateFor P m') :
    m = m' := by
  obtain ⟨hm, hp, hmin⟩ := h
  obtain ⟨hm', hp', hmin'⟩ := h'
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exact absurd hp (hmin' m hm hlt)
  · exact heq
  · exact absurd hp' (hmin m' hm' hgt)

