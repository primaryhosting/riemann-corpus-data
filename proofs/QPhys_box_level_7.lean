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

namespace QPhys

/-- Energy levels of a particle of mass `m` in a one-dimensional infinite
potential well ("particle in a box") of width `L`, with reduced Planck
constant `hbar`:  `Eₙ = n² π² ħ² / (2 m L²)`, for `n ≥ 1`. -/
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- For the one-dimensional infinite well, the ratio of the seventh energy
level to the ground-state energy is `7² = 49`, for any positive mass `m`,
well width `L` and nonzero `ħ`. -/
theorem box_level_7 (hbar m L : ℝ) (hhbar : hbar ≠ 0) (hm : 0 < m) (hL : 0 < L) :
    boxEnergy hbar m L 7 / boxEnergy hbar m L 1 = (7 : ℝ) ^ 2 := by
  have hden : (2 * m * L ^ 2 : ℝ) ≠ 0 := by positivity
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have hE1 : boxEnergy hbar m L 1 ≠ 0 := by
    simp only [boxEnergy]
    exact div_ne_zero (by positivity) hden
  rw [div_eq_iff hE1]
  simp only [boxEnergy]
  field_simp
  ring

end QPhys


