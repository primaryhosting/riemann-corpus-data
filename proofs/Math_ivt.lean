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

namespace Math

/-- **Intermediate value theorem.** A function continuous on `[a, b]` attains every value
between `f a` and `f b`: for any `y` in the interval spanned by `f a` and `f b`, there is
`c ∈ [a, b]` with `f c = y`. -/
theorem ivt {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    {y : ℝ} (hy : y ∈ Set.uIcc (f a) (f b)) : ∃ c ∈ Set.Icc a b, f c = y := by
  have h : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  obtain ⟨c, hc, hfc⟩ := intermediate_value_uIcc (f := f) (a := a) (b := b)
    (by rw [h]; exact hf) hy
  exact ⟨c, by rwa [h] at hc, hfc⟩

end Math

