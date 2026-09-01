/-
# Coboundary Of Sum Eq
Category: B Brockian Frontier
Target: Brockian.PhaseDepthCohomologyComplete.coboundary_of_sum_eq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian
namespace PhaseDepthCohomologyComplete

/-- **Completeness half of the discrete-cohomology no-go on the 5-cycle.**
If `c1 c2 : ZMod 5 → G` have equal total sums, then their difference is a coboundary:
there is `h : ZMod 5 → G` with `c1 j - c2 j = h (j + 1) - h j` for every `j`.

The witness is the partial-sum function of `g j = c1 j - c2 j`
(`h 0 = 0`, `h 1 = g 0`, ..., `h 4 = g 0 + g 1 + g 2 + g 3`); the seam at `j = 4`
closes precisely because `∑ j, g j = 0`. -/
theorem coboundary_of_sum_eq {G : Type*} [AddCommGroup G] (c1 c2 : ZMod 5 → G)
    (hs : (Finset.univ.sum c1) = (Finset.univ.sum c2)) :
    ∃ h : ZMod 5 → G, ∀ j, c1 j - c2 j = h (j + 1) - h j := by
  set g : ZMod 5 → G := fun j => c1 j - c2 j with hg
  have hzero : g 0 + g 1 + g 2 + g 3 + g 4 = 0 := by
    have h0 : Finset.univ.sum g = 0 := by
      simp [hg, Finset.sum_sub_distrib, hs]
    rw [show (Finset.univ.sum g) = g 0 + g 1 + g 2 + g 3 + g 4 by
      show ∑ i : Fin 5, g i = _
      rw [Fin.sum_univ_five]] at h0
    exact h0
  refine ⟨fun k => (![0, g 0, g 0 + g 1, g 0 + g 1 + g 2, g 0 + g 1 + g 2 + g 3] : Fin 5 → G) k, ?_⟩
  intro j
  fin_cases j
  · show g 0 = g 0 - 0
    abel
  · show g 1 = (g 0 + g 1) - g 0
    abel
  · show g 2 = (g 0 + g 1 + g 2) - (g 0 + g 1)
    abel
  · show g 3 = (g 0 + g 1 + g 2 + g 3) - (g 0 + g 1 + g 2)
    abel
  · show g 4 = 0 - (g 0 + g 1 + g 2 + g 3)
    linear_combination (norm := abel) hzero

end PhaseDepthCohomologyComplete
end Brockian

#print axioms Brockian.PhaseDepthCohomologyComplete.coboundary_of_sum_eq

