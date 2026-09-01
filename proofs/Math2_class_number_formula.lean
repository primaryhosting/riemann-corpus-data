/-
# Class Number Formula
Category: Frontier Math
Target: Math2.class_number_formula
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` commands to precede any module docstring, so the header above
-- is written as a plain block comment; its text is unchanged.)

import Mathlib

open scoped BigOperators Real Nat Classical Pointwise

open Filter Topology NumberField NumberField.InfinitePlace NumberField.Units

namespace Math2

/--
**The analytic class number formula.**

For a number field `K`, the Dedekind zeta function `ζ_K` has a simple pole at `s = 1`
whose residue is
`(2 ^ r₁ * (2 π) ^ r₂ * Reg_K * h_K) / (w_K * √|d_K|)`,
where `r₁` (resp. `r₂`) is the number of real (resp. complex) places of `K`, `Reg_K` is the
regulator, `h_K` the class number, `w_K` the number of roots of unity in `K`, and `d_K` the
discriminant.
-/
theorem class_number_formula (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun s : ℝ ↦ (s - 1) * dedekindZeta K s) (𝓝[>] 1)
      (𝓝 (((2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K * classNumber K) /
        (torsionOrder K * Real.sqrt |(discr K : ℝ)|) : ℝ) : ℂ)) := by
  simpa only [dedekindZeta_residue_def] using tendsto_sub_one_mul_dedekindZeta_nhdsGT K

end Math2

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

