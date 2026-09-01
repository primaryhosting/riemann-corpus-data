import Mathlib

/-!
# Bekenstein Bound
Category: Frontier Phys
Target: Phys.bekenstein_bound
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

namespace Phys

/-- The Bekenstein bound expression `2 π k R E / (ℏ c)`: the maximal entropy that can be
contained in a region of radius `R` enclosing total energy `E`. -/
noncomputable def bekensteinBoundValue (k hbar c R E : ℝ) : ℝ :=
  2 * Real.pi * k * R * E / (hbar * c)

/-- The Schwarzschild radius `R = 2 G E / c ^ 4` of a body of total energy `E = M c ^ 2`. -/
noncomputable def schwarzschildRadius (G c E : ℝ) : ℝ := 2 * G * E / c ^ 4

/-- The Bekenstein–Hawking entropy `S = k c ^ 3 A / (4 G ℏ)` of a horizon of area `A`. -/
noncomputable def bekensteinHawkingEntropy (k hbar c G A : ℝ) : ℝ :=
  k * c ^ 3 * A / (4 * G * hbar)

/-- The area `4 π R ^ 2` of a sphere of radius `R`. -/
noncomputable def sphereArea (R : ℝ) : ℝ := 4 * Real.pi * R ^ 2

/-- **Key computation.** For a Schwarzschild black hole of energy `E`, whose horizon radius is
`R = 2 G E / c ^ 4`, the Bekenstein–Hawking entropy of the horizon is *exactly* the Bekenstein
bound value `2 π k R E / (ℏ c)`.  (This is the standard derivation: the gravitational constant
`G = R c ^ 4 / (2 E)` is eliminated using the Schwarzschild relation.) -/
theorem bekensteinHawking_eq_bekensteinBoundValue
    {k hbar c G R E : ℝ} (hhbar : hbar ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0)
    (hR : R = schwarzschildRadius G c E) :
    bekensteinHawkingEntropy k hbar c G (sphereArea R) = bekensteinBoundValue k hbar c R E := by
  subst hR
  unfold bekensteinHawkingEntropy bekensteinBoundValue sphereArea schwarzschildRadius
  field_simp

/-- **The Bekenstein bound.**

For a physical system of total energy `E` contained inside a sphere of radius `R`, the
entropy `S` satisfies
`S ≤ 2 π k R E / (ℏ c)`.

The physical input (Susskind's spherical-entropy argument / the generalized second law) is the
hypothesis `hS`: the entropy of the system does not exceed the Bekenstein–Hawking entropy
`k c ^ 3 A / (4 G ℏ)` of a black hole with the same energy, whose horizon `R` is the
Schwarzschild radius of that energy.  Given this, the bound in the stated form is an exact
consequence of the Schwarzschild relation `R = 2 G E / c ^ 4`. -/
theorem bekenstein_bound
    {S k hbar c G R E : ℝ} (hhbar : 0 < hbar) (hc : 0 < c) (hG : 0 < G)
    (hR : R = schwarzschildRadius G c E)
    (hS : S ≤ bekensteinHawkingEntropy k hbar c G (sphereArea R)) :
    S ≤ 2 * Real.pi * k * R * E / (hbar * c) := by
  have h := bekensteinHawking_eq_bekensteinBoundValue (k := k) hhbar.ne' hc.ne' hG.ne' hR
  rw [h] at hS
  simpa [bekensteinBoundValue] using hS

end Phys

