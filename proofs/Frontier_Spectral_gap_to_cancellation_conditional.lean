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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier.Spectral

/-- **Gap to cancellation, conditional form.**

Setting: a real inner-product space `V`, a self-adjoint projection `P` (the gap projection),
a unit vector `u`, and a real number `S` (the Liouville partial sum).

Hypotheses (both kept open, neither is discharged):

* `H1` : a spectral gap `δ > 0` together with the identity `S = ⟪u, P u⟫_ℝ`;
* `H2` : the contraction bound `‖P u‖ ≤ 1 - δ`.

Conclusion: `|S| ≤ 1 - δ`.

The proof is Cauchy–Schwarz: `|⟪u, P u⟫| ≤ ‖u‖ * ‖P u‖ = ‖P u‖ ≤ 1 - δ`.

The structural hypotheses on `P` (self-adjointness `hsa` and idempotence `hidem`) and the
positivity `hδ` of the gap are part of the requested statement; they are retained even though
the Cauchy–Schwarz argument does not need them. -/
theorem gap_to_cancellation_conditional
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : V →ₗ[ℝ] V)
    (hsa : ∀ x y : V, (inner ℝ (P x) y : ℝ) = (inner ℝ x (P y) : ℝ))
    (hidem : ∀ x : V, P (P x) = P x)
    (u : V) (hu : ‖u‖ = 1)
    (S δ : ℝ) (hδ : 0 < δ)
    (hS : S = (inner ℝ u (P u) : ℝ))
    (hcontr : ‖P u‖ ≤ 1 - δ) :
    |S| ≤ 1 - δ := by
  rw [hS]
  calc |(inner ℝ u (P u) : ℝ)| ≤ ‖u‖ * ‖P u‖ := abs_real_inner_le_norm u (P u)
    _ = ‖P u‖ := by rw [hu, one_mul]
    _ ≤ 1 - δ := hcontr

end Frontier.Spectral

#print axioms Frontier.Spectral.gap_to_cancellation_conditional

