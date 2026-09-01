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

/-
# Cycle Gap Vanishes
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_gap_vanishes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cycle Gap Vanishes
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_gap_vanishes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real

namespace Frontier.Spectral

/-- The Fiedler value (algebraic connectivity) of the cycle graph `C n`. -/
noncomputable def g (n : ℕ) : ℝ := 2 - 2 * Real.cos (2 * Real.pi / n)

/-- The angle `2π/n` tends to `0` as `n → ∞`. -/
theorem tendsto_angle_atTop :
    Filter.Tendsto (fun n : ℕ => 2 * Real.pi / n) Filter.atTop (nhds 0) :=
  Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop

/-- The Fiedler value of the cycle `C n` vanishes as `n → ∞`, so the plain cycle
family has no uniform spectral gap. -/
theorem cycle_gap_vanishes :
    Filter.Tendsto g Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun n : ℕ => 2 - 2 * Real.cos (2 * Real.pi / n))
      Filter.atTop (nhds (2 - 2 * Real.cos 0)) :=
    Filter.Tendsto.const_sub _
      (((Real.continuous_cos.tendsto 0).comp tendsto_angle_atTop).const_mul 2)
  simpa [g, Real.cos_zero] using h

end Frontier.Spectral

