import Mathlib

/-!
# Banach Fixed Point
Category: Frontier Wave 2 (deeper machinery)
Target: Analysis.banach_fixed_point
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

/-- **Banach fixed-point theorem**: a contraction `f` with constant `K` on a nonempty
complete metric space has a unique fixed point, namely `ContractingWith.fixedPoint f hf`. -/
theorem banach_fixed_point {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {K : NNReal} {f : X → X} (hf : ContractingWith K f) :
    f (ContractingWith.fixedPoint f hf) = ContractingWith.fixedPoint f hf ∧
      ∀ y : X, f y = y → y = ContractingWith.fixedPoint f hf := by
  refine ⟨hf.fixedPoint_isFixedPt, fun y hy => ?_⟩
  exact hf.fixedPoint_unique hy

end Analysis

