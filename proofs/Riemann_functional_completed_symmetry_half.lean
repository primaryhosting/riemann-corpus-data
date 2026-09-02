import Mathlib

/-!
# Completed Symmetry Half
Category: Riemann Program
Target: Riemann.functional.completed_symmetry_half
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.functional

/-- At the center of symmetry `s = 1/2`, the functional equation for the completed
Riemann zeta function is trivially self-consistent, since `1 - 1/2 = 1/2`. Hence
`completedRiemannZeta (1 - 1/2) = completedRiemannZeta (1/2)`.

(Equivalently, this is the fixed point of the involution `s ↦ 1 - s` under which
`completedRiemannZeta` is symmetric.) -/
theorem completed_symmetry_half :
    completedRiemannZeta (1 - (1 / 2 : ℂ)) = completedRiemannZeta (1 / 2 : ℂ) := by
  norm_num

end Riemann.functional

