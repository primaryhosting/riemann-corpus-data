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

namespace LargeSieve

/-- The (unnormalized) discrete Fourier transform on `ZMod q`. -/
noncomputable def fourier {q : ℕ} [NeZero q] (f : ZMod q → ℂ) : ZMod q → ℂ := ZMod.dft f

/-- The Fourier energy carried by any finite sub-collection `S` of frequencies is at most
the total Fourier energy. -/
theorem fourier_sq_sum_le {q : ℕ} [NeZero q] (f : ZMod q → ℂ)
    (S : Finset (ZMod q)) :
    ∑ k ∈ S, ‖fourier f k‖ ^ 2 ≤ ∑ k : ZMod q, ‖fourier f k‖ ^ 2 := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
  intro i _ _
  positivity

end LargeSieve

