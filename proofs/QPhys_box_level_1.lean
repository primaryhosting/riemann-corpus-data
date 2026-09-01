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

/-- Energy of the `n`-th level of a particle of mass `m` in a one-dimensional
infinite square well (particle in a box) of width `L`, with reduced Planck
constant `hbar`:  `E n = n^2 * π^2 * hbar^2 / (2 * m * L^2)`. -/
noncomputable def boxEnergy (m L hbar : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- For a particle in a one-dimensional infinite well with positive mass, width
and reduced Planck constant, the ratio of the ground-state energy to itself is
`1 ^ 2 = 1`. -/
theorem box_level_1 (m L hbar : ℝ) (hm : 0 < m) (hL : 0 < L) (hbar_pos : 0 < hbar) :
    boxEnergy m L hbar 1 / boxEnergy m L hbar 1 = (1 : ℝ) ^ 2 := by
  have h1 : boxEnergy m L hbar 1 ≠ 0 := by
    unfold boxEnergy
    have : (0:ℝ) < (1 : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2) := by
      have := Real.pi_pos
      positivity
    simpa using ne_of_gt this
  rw [div_self h1]
  norm_num

end QPhys

