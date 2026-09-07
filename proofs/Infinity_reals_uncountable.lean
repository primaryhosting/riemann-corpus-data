import Mathlib

/-!
# Reals Uncountable
Category: Frontier — Set Theory
Target: Infinity.reals_uncountable
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

namespace Infinity

/-- The real numbers are not a countable type. -/
theorem real_not_countable : ¬ Countable ℝ := fun h =>
  Cardinal.not_countable_real (Set.countable_univ_iff.mpr h)

/-- The real numbers are uncountable: there is no surjection from `ℕ` onto `ℝ`. -/
theorem reals_uncountable : ¬ ∃ f : ℕ → ℝ, Function.Surjective f := by
  rintro ⟨f, hf⟩
  exact real_not_countable (Function.Surjective.countable hf)

end Infinity

