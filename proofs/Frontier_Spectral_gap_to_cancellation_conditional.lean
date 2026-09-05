import Mathlib

/-!
# Gap To Cancellation Conditional
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.gap_to_cancellation_conditional
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

set_option grind.warning false

namespace Frontier.Spectral

/-- **Conditional cancellation bridge.**

Setting: a real inner-product space `V`, a self-adjoint projection `P` (the gap projection),
a unit vector `u`, and a real number `S` (the Liouville partial sum).

Hypotheses (both kept open, neither discharged):
* `H1` : there is a spectral gap `delta > 0` and `S = ⟪u, P u⟫`;
* `H2` : the contraction bound `‖P u‖ ≤ 1 - delta`.

Note: the structural hypotheses `hsa`, `hidem` (P is a self-adjoint projection) and
`hdelta` (positive gap) are part of the requested setting; the bound follows from `H1`, `H2`
and `hu` alone, so they are not used in the proof.

Conclusion: `|S| ≤ 1 - delta`.
-/
theorem gap_to_cancellation_conditional
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : V →ₗ[ℝ] V) (hsa : ∀ x y : V, inner ℝ (P x) y = inner ℝ x (P y))
    (hidem : ∀ x : V, P (P x) = P x)
    (u : V) (hu : ‖u‖ = 1) (S delta : ℝ) (hdelta : 0 < delta)
    (H1 : S = inner ℝ u (P u)) (H2 : ‖P u‖ ≤ 1 - delta) :
    |S| ≤ 1 - delta := by
  have h := abs_real_inner_le_norm u (P u)
  rw [H1]
  calc |inner ℝ u (P u)| ≤ ‖u‖ * ‖P u‖ := h
    _ = ‖P u‖ := by rw [hu, one_mul]
    _ ≤ 1 - delta := H2

end Frontier.Spectral

#print axioms Frontier.Spectral.gap_to_cancellation_conditional

