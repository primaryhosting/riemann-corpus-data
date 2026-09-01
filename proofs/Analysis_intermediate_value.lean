import Mathlib

/-!
# Intermediate Value
Category: Frontier Wave 2 (deeper machinery)
Target: Analysis.intermediate_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Analysis

/-- **Intermediate value theorem.** If `a ≤ b` and `f : ℝ → ℝ` is continuous on `Set.Icc a b`,
then every value between `f a` and `f b` is attained by `f` on `Set.Icc a b`. -/
theorem intermediate_value {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    Set.Icc (f a) (f b) ⊆ f '' Set.Icc a b :=
  intermediate_value_Icc hab hf

end Analysis

