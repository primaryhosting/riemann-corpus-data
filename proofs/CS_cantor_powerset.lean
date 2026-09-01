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

/-- **Cantor's theorem**: there is no surjection from a type `A` onto its
powerset `𝒫 A = Set A`.  Proved by the diagonal argument: the set
`{a | a ∉ f a}` is not in the range of `f`. -/
theorem cantor_powerset {A : Type*} (f : A → Set A) : ¬ Function.Surjective f := by
  intro hf
  obtain ⟨a, ha⟩ := hf {x | x ∉ f x}
  have h : a ∈ ({x | x ∉ f x} : Set A) ↔ a ∈ f a := by rw [ha]
  simp only [Set.mem_setOf_eq] at h
  tauto

end CS

