import Mathlib
/-!
# Box Level 3
Category: Quantum Physics
Target: QPhys.box_level_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- Energy of the `n`-th stationary state of a particle of mass `m` in a
one-dimensional infinite potential well ("particle in a box") of width `L`,
with reduced Planck constant `hbar`:
`Eₙ = n² π² ħ² / (2 m L²)`. -/
noncomputable def boxEnergy (hbar m L : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 * Real.pi ^ 2 * hbar ^ 2 / (2 * m * L ^ 2)

/-- Every level is `n²` times the ground-state energy:
`Eₙ = n² E₁`. -/
theorem boxEnergy_eq_sq_mul_boxEnergy_one (hbar m L : ℝ) (n : ℕ) :
    boxEnergy hbar m L n = (n : ℝ) ^ 2 * boxEnergy hbar m L 1 := by
  unfold boxEnergy
  push_cast
  ring

/-- For the infinite square well, the ratio of the third energy level to the
ground-state energy is `E₃ / E₁ = 3²` (i.e. `9`). -/
theorem box_level_3 (hbar m L : ℝ) (hhbar : hbar ≠ 0) (hm : m ≠ 0) (hL : L ≠ 0) :
    boxEnergy hbar m L 3 / boxEnergy hbar m L 1 = 3 ^ 2 := by
  have h1 : boxEnergy hbar m L 1 ≠ 0 := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    unfold boxEnergy
    positivity
  rw [boxEnergy_eq_sq_mul_boxEnergy_one hbar m L 3]
  rw [mul_div_assoc, div_self h1, mul_one]
  norm_num

end QPhys

