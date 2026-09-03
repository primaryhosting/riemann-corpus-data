import Mathlib

/-!
# Reals Uncountable
Category: Frontier — Set Theory
Target: Infinity.reals_uncountable
Verification: verified (axiom-clean: propext, Classical.choice, Quot.sound)
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Infinity

/-- The real numbers are uncountable: there is no surjection from `ℕ` onto `ℝ`,
and equivalently `ℝ` is not a countable type. -/
theorem reals_uncountable :
    (¬ ∃ f : ℕ → ℝ, Function.Surjective f) ∧ ¬ Countable ℝ := by
  have h : ¬ Countable ℝ := Uncountable.not_countable
  exact ⟨fun ⟨_, hf⟩ => h hf.countable, h⟩

end Infinity

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

