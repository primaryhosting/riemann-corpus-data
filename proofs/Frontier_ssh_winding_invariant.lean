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

namespace Frontier

open Complex Metric

/-- The off-diagonal entry of the Bloch Hamiltonian of the Su–Schrieffer–Heeger (SSH) chain
with intracell hopping `v` and intercell hopping `w`:
`h(k) = v + w e^{i k}`.  The full Bloch Hamiltonian is `H(k) = Re h(k) • σₓ + Im h(k) • σ_y`,
so the spectral gap is open exactly when `h(k) ≠ 0` for all `k`. -/
noncomputable def sshBloch (v w : ℝ) (k : ℝ) : ℂ :=
  (v : ℂ) + (w : ℂ) * Complex.exp (k * Complex.I)

/-- The winding number of the SSH loop `k ↦ h(k)` around the origin,
`(2π i)⁻¹ ∫₀^{2π} h'(k)/h(k) dk`. -/
noncomputable def sshWinding (v w : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I)⁻¹ *
    ∫ k in (0 : ℝ)..(2 * Real.pi), deriv (sshBloch v w) k / sshBloch v w k

lemma sshBloch_eq_circleMap (v w : ℝ) : sshBloch v w = circleMap (v : ℂ) w := by
  funext k
  simp [sshBloch, circleMap, mul_comm]

/-- The winding number is `(2π i)⁻¹` times the contour integral of `z⁻¹` over the circle
of radius `w` centered at `v`, which is precisely the image of the SSH loop. -/
lemma sshWinding_eq_circleIntegral (v w : ℝ) :
    sshWinding v w = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∮ z in C((v : ℂ), w), z⁻¹ := by
  rw [sshWinding, sshBloch_eq_circleMap, circleIntegral]
  congr 1

/-- **Topological phase** (`|v| < w`): the SSH winding number equals `1`. -/
theorem sshWinding_of_abs_lt (v w : ℝ) (h : |v| < w) : sshWinding v w = 1 := by
  have hmem : (0 : ℂ) ∈ ball ((v : ℂ)) w := by
    simp only [mem_ball, dist_eq, zero_sub, norm_neg]
    simpa using h
  have := circleIntegral.integral_sub_inv_of_mem_ball hmem
  simp only [sub_zero] at this
  rw [sshWinding_eq_circleIntegral, this]
  field_simp

/-- **Trivial phase** (`w < |v|`): the SSH winding number equals `0`. -/
theorem sshWinding_of_lt_abs (v w : ℝ) (hw : 0 ≤ w) (h : w < |v|) : sshWinding v w = 0 := by
  have hne : ∀ z ∈ closedBall ((v : ℂ)) w, z ≠ 0 := by
    intro z hz hz0
    rw [mem_closedBall, dist_eq, hz0] at hz
    have : |v| ≤ w := by simpa using hz
    exact absurd h (not_lt.mpr this)
  have hcont : ContinuousOn (fun z : ℂ => z⁻¹) (closedBall ((v : ℂ)) w) :=
    fun z hz => (continuousAt_inv₀ (hne z hz)).continuousWithinAt
  have hzero : (∮ z in C((v : ℂ), w), z⁻¹) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hw
      (Set.countable_empty) hcont
      (fun z hz => differentiableAt_inv_iff.mpr (hne z (ball_subset_closedBall hz.1)))
  rw [sshWinding_eq_circleIntegral, hzero, mul_zero]

/-- **The SSH topological invariant.**  For `|v| ≠ w` (an open gap) the winding number of the
Bloch loop `k ↦ v + w e^{ik}` around the origin is an integer, equal to `1` in the topological
phase `|v| < w` and to `0` in the trivial phase `w < |v|`. -/
theorem ssh_winding_invariant (v w : ℝ) (hw : 0 ≤ w) (h : |v| ≠ w) :
    sshWinding v w = if |v| < w then (1 : ℂ) else 0 := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [if_pos hlt, sshWinding_of_abs_lt v w hlt]
  · rw [if_neg (not_lt.mpr hgt.le), sshWinding_of_lt_abs v w hw hgt]

/-- The SSH winding number always takes values in `ℤ` (when the gap is open). -/
theorem ssh_winding_integer (v w : ℝ) (hw : 0 ≤ w) (h : |v| ≠ w) :
    ∃ n : ℤ, sshWinding v w = (n : ℂ) := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact ⟨1, by rw [sshWinding_of_abs_lt v w hlt]; norm_num⟩
  · exact ⟨0, by rw [sshWinding_of_lt_abs v w hw hgt]; norm_num⟩

end Frontier

