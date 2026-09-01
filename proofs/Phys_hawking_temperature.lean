/-
# Hawking Temperature
Category: Frontier Phys
Target: Phys.hawking_temperature
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hawking Temperature
Category: Frontier Phys
Target: Phys.hawking_temperature
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- The surface gravity `κ = c⁴ / (4 G M)` at the horizon `r = 2GM/c²` of a
Schwarzschild black hole of mass `M`. -/
noncomputable def surfaceGravity (G M c : ℝ) : ℝ := c ^ 4 / (4 * G * M)

/-- The Hawking–Unruh relation between the temperature of a horizon and its
surface gravity: `T = ℏ κ / (2 π c k_B)`. -/
noncomputable def temperatureOfSurfaceGravity (hbar kappa c kB : ℝ) : ℝ :=
  hbar * kappa / (2 * Real.pi * c * kB)

/-- **Hawking temperature of a Schwarzschild black hole.**

Feeding the Schwarzschild surface gravity `κ = c⁴/(4GM)` into the Hawking–Unruh
relation `T = ℏκ/(2πck_B)` gives

`T = ℏ c³ / (8 π G M k_B)`. -/
theorem hawking_temperature (hbar c G M kB : ℝ)
    (hc : c ≠ 0) (hG : G ≠ 0) (hM : M ≠ 0) (hkB : kB ≠ 0) :
    temperatureOfSurfaceGravity hbar (surfaceGravity G M c) c kB
      = hbar * c ^ 3 / (8 * Real.pi * G * M * kB) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold temperatureOfSurfaceGravity surfaceGravity
  field_simp
  ring

/-- The Hawking temperature is strictly positive for positive physical constants
and positive mass. -/
theorem hawking_temperature_pos (hbar c G M kB : ℝ)
    (hbar_pos : 0 < hbar) (hc : 0 < c) (hG : 0 < G) (hM : 0 < M) (hkB : 0 < kB) :
    0 < temperatureOfSurfaceGravity hbar (surfaceGravity G M c) c kB := by
  rw [hawking_temperature hbar c G M kB hc.ne' hG.ne' hM.ne' hkB.ne']
  have hpi : 0 < Real.pi := Real.pi_pos
  positivity

/-- The Hawking temperature is inversely proportional to the mass: doubling the
mass halves the temperature. -/
theorem hawking_temperature_inverse_mass (hbar c G M kB : ℝ)
    (hc : c ≠ 0) (hG : G ≠ 0) (hM : M ≠ 0) (hkB : kB ≠ 0) :
    temperatureOfSurfaceGravity hbar (surfaceGravity G (2 * M) c) c kB
      = temperatureOfSurfaceGravity hbar (surfaceGravity G M c) c kB / 2 := by
  rw [hawking_temperature hbar c G (2 * M) kB hc hG (by simpa using hM) hkB,
    hawking_temperature hbar c G M kB hc hG hM hkB]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

end Phys

