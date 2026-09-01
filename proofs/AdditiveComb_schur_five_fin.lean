/-
# Schur Five
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.schur_five
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Schur Five
Category: Frontier Wave 2 (deeper machinery)
Target: AdditiveComb.schur_five
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace AdditiveComb

/-- The Schur instance on `{1,2,3,4,5}` phrased for colourings indexed by `Fin 5`,
where the index `i` stands for the integer `i + 1`.  Proved by exhaustive check over
the `2^5 = 32` colourings. -/
theorem schur_five_fin (g : Fin 5 → Bool) :
    ∃ x y z : Fin 5,
      ((x : ℕ) + 1) + ((y : ℕ) + 1) = (z : ℕ) + 1 ∧ g x = g y ∧ g y = g z := by
  revert g
  decide

/-- **Schur's theorem, the instance `S(2) < 5`.**
For every `2`-colouring `f` of `{1,2,3,4,5}` there is a monochromatic Schur triple:
elements `x, y, z ∈ {1,…,5}` with `x + y = z` and `f x = f y = f z`. -/
theorem schur_five (f : ℕ → Bool) :
    ∃ x ∈ Finset.Icc 1 5, ∃ y ∈ Finset.Icc 1 5, ∃ z ∈ Finset.Icc 1 5,
      x + y = z ∧ f x = f y ∧ f y = f z := by
  obtain ⟨x, y, z, hsum, hxy, hyz⟩ := schur_five_fin (fun i => f ((i : ℕ) + 1))
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  refine ⟨(x : ℕ) + 1, ?_, (y : ℕ) + 1, ?_, (z : ℕ) + 1, ?_, hsum, hxy, hyz⟩ <;>
    simp only [Finset.mem_Icc] <;> omega

end AdditiveComb

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

