import Mathlib

/-!
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Module

/-- Number of intensive state variables used to describe a system of `C` chemical
components distributed over `P` phases: temperature, pressure, and the `C` mole
fractions of each of the `P` phases. -/
def numVariables (C P : ℕ) : ℕ := 2 + P * C

/-- Number of equilibrium constraints on the intensive variables: one normalisation
condition `∑ᵢ xᵢⱼ = 1` per phase (`P` of them), together with the equalities of the
chemical potential of each component across the phases (`C * (P - 1)` of them). -/
def numConstraints (C P : ℕ) : ℕ := P + C * (P - 1)

/-- The counting identity behind the phase rule:
`(2 + P·C) - (P + C·(P-1)) = C - P + 2`. -/
theorem numVariables_sub_numConstraints (C P : ℕ) (hP : 1 ≤ P) :
    (numVariables C P : ℤ) - (numConstraints C P : ℤ) = (C : ℤ) - (P : ℤ) + 2 := by
  unfold numVariables numConstraints
  have h : ((P - 1 : ℕ) : ℤ) = (P : ℤ) - 1 := by
    push_cast [Nat.cast_sub hP]
    ring
  push_cast [h]
  ring

/-- **Gibbs phase rule.**

The intensive state of a system of `C` components in `P` phases is described by a point
of `ℝ ^ (2 + P·C)` (temperature, pressure, and the mole fractions), subject to a system
of `P + C·(P-1)` independent equilibrium constraints, encoded by a surjective linear map
`f` whose fibres are the admissible states.  The number of degrees of freedom is the
affine dimension of such a fibre, i.e. the dimension of `ker f`, and it equals
`F = C - P + 2`. -/
theorem gibbs_phase_rule (C P : ℕ) (hP : 1 ≤ P)
    (f : (Fin (numVariables C P) → ℝ) →ₗ[ℝ] (Fin (numConstraints C P) → ℝ))
    (hf : Function.Surjective f) :
    (finrank ℝ (LinearMap.ker f) : ℤ) = (C : ℤ) - (P : ℤ) + 2 := by
  have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.2 hf
  have hsum : finrank ℝ (LinearMap.range f) + finrank ℝ (LinearMap.ker f)
      = finrank ℝ (Fin (numVariables C P) → ℝ) :=
    LinearMap.finrank_range_add_finrank_ker f
  have hr : finrank ℝ (LinearMap.range f) = numConstraints C P := by
    rw [hrange]
    simp [finrank_top]
  have hv : finrank ℝ (Fin (numVariables C P) → ℝ) = numVariables C P := by
    simp
  rw [hr, hv] at hsum
  have : (finrank ℝ (LinearMap.ker f) : ℤ)
      = (numVariables C P : ℤ) - (numConstraints C P : ℤ) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) hsum
    push_cast at this
    linarith
  rw [this, numVariables_sub_numConstraints C P hP]

end Chem

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

