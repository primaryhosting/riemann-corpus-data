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

namespace CS

/-- Pigeonhole principle for hash functions: any function from a type with `n+1`
elements to a type with `n` elements has a collision, i.e. two distinct inputs
mapping to the same output. -/
theorem pigeonhole_hash {α β : Type*} [Fintype α] [Fintype β] {n : ℕ}
    (hα : Fintype.card α = n + 1) (hβ : Fintype.card β = n) (h : α → β) :
    ∃ x y : α, x ≠ y ∧ h x = h y := by
  have hlt : Fintype.card β < Fintype.card α := by omega
  obtain ⟨x, y, hxy, hh⟩ := Fintype.exists_ne_map_eq_of_card_lt h hlt
  exact ⟨x, y, hxy, hh⟩

end CS

