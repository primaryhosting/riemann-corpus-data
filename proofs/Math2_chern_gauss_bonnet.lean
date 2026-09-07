/-
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Chern Gauss Bonnet
Category: Frontier Math
Target: Math2.chern_gauss_bonnet
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

set_option grind.warning false

namespace Math2

open MeasureTheory Metric Set

/-- The value of the Pfaffian (Euler) form of the Riemann curvature operator of a Riemannian
manifold of even dimension `2 * n` and constant sectional curvature `1`, measured against the
Riemannian volume form.

For constant sectional curvature `1` the curvature two-forms in an orthonormal coframe are
`Ω i j = e i ∧ e j`, and the classical Pfaffian
`Pf(Ω) = (2 ^ n * n !)⁻¹ * ∑ σ, sign σ • Ω (σ 1) (σ 2) ∧ ⋯ ∧ Ω (σ (2 * n - 1)) (σ (2 * n))`
evaluates to `(2 * n)! / (2 ^ n * n !)` times the volume form.  (For `n = 1` this is the
Gaussian curvature `K = 1` of the unit two-sphere.) -/
noncomputable def pfaffianConstCurv (n : ℕ) : ℝ := (2 * n)! / (2 ^ n * n !)

/-- The Riemannian volume of the round `2 * n`-dimensional sphere of radius `r`, i.e. of the
sphere of radius `r` in the Euclidean space `ℝ ^ (2 * n + 1)`.

It is defined as the derivative in `r` of the volume of the ball of radius `r`, that is
`(2 * n + 1) * vol (ball 0 r) / r`; `roundSphereVolume_one` below identifies the value at
`r = 1` with Mathlib's spherical measure `MeasureTheory.Measure.toSphere` of the unit sphere. -/
noncomputable def roundSphereVolume (n : ℕ) (r : ℝ) : ℝ :=
  (2 * n + 1) * (volume (ball (0 : EuclideanSpace ℝ (Fin (2 * n + 1))) r)).toReal / r

lemma finrank_euclidean (m : ℕ) : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by
  simp

/-- At radius `1`, `roundSphereVolume` agrees with the canonical measure of the unit sphere
obtained from Lebesgue measure by the polar coordinate decomposition. -/
lemma roundSphereVolume_one (n : ℕ) :
    roundSphereVolume n 1 =
      (Measure.toSphere (volume : Measure (EuclideanSpace ℝ (Fin (2 * n + 1))))).real univ := by
  rw [Measure.toSphere_real_apply_univ, finrank_euclidean, roundSphereVolume]
  simp [measureReal_def]

/-- Closed form for the volume of a ball of radius `r` in odd-dimensional Euclidean space. -/
lemma volume_ball_odd (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    (volume (ball (0 : EuclideanSpace ℝ (Fin (2 * n + 1))) r)).toReal =
      r ^ (2 * n + 1) * (Real.pi ^ n * 2 ^ (n + 1) / (2 * n + 1)‼) := by
  rw [EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin]
  have hG : Real.Gamma ((2 * n + 1 : ℕ) / 2 + 1)
      = ((2 * (n + 1) - 1)‼ : ℕ) * Real.sqrt Real.pi / 2 ^ (n + 1) := by
    rw [← Real.Gamma_nat_add_half (n + 1)]
    congr 1
    push_cast
    ring
  have hpi : Real.sqrt Real.pi ^ (2 * n + 1) = Real.pi ^ n * Real.sqrt Real.pi := by
    rw [pow_succ, pow_mul, Real.sq_sqrt Real.pi_nonneg]
  have h2 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  have hs : Real.sqrt Real.pi > 0 := Real.sqrt_pos.2 Real.pi_pos
  have hd : ((2 * n + 1)‼ : ℝ) > 0 := by positivity
  rw [hG, hpi, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.toReal_ofReal]
  · rw [h2]
    field_simp
  · rw [h2]
    positivity

/-- Closed form for the Riemannian volume of the round `2 * n`-sphere of radius `r`:
`vol = (2 * n + 1) * 2 ^ (n + 1) * π ^ n / (2 * n + 1)‼ * r ^ (2 * n)`. -/
lemma roundSphereVolume_eq (n : ℕ) {r : ℝ} (hr : 0 < r) :
    roundSphereVolume n r =
      (2 * n + 1) * r ^ (2 * n) * (Real.pi ^ n * 2 ^ (n + 1) / (2 * n + 1)‼) := by
  rw [roundSphereVolume, volume_ball_odd n hr.le]
  field_simp
  ring

/-- `(2 * n + 1)‼ * (2 ^ n * n !) = (2 * n + 1)!`. -/
lemma doubleFactorial_odd_mul (n : ℕ) : (2 * n + 1)‼ * (2 ^ n * n !) = (2 * n + 1)! := by
  have h := Nat.factorial_eq_mul_doubleFactorial (2 * n)
  rw [Nat.doubleFactorial_two_mul] at h
  omega

/-- Sanity check: the unit two-sphere has area `4 * π`. -/
lemma roundSphereVolume_one_one : roundSphereVolume 1 1 = 4 * Real.pi := by
  rw [roundSphereVolume_eq 1 one_pos]
  norm_num [Nat.doubleFactorial]
  ring

/-- Sanity check: the unit four-sphere has volume `8 * π ^ 2 / 3`. -/
lemma roundSphereVolume_two_one : roundSphereVolume 2 1 = 8 * Real.pi ^ 2 / 3 := by
  rw [roundSphereVolume_eq 2 one_pos]
  norm_num [Nat.doubleFactorial]
  ring

/-- **Chern–Gauss–Bonnet** for the round spheres `S ^ (2 * n)` of arbitrary radius `r > 0`
(the constant-curvature case of the theorem, in every even dimension).

The left-hand side is the Gauss–Bonnet integrand `(2 * π) ^ (-n) * Pf(Ω)` integrated over the
manifold: the sphere of radius `r` has constant sectional curvature `r ^ (-2)`, so the Pfaffian
of its curvature form is `pfaffianConstCurv n / r ^ (2 * n)` times the Riemannian volume form,
and its integral is that constant times the total volume `roundSphereVolume n r`.  The
right-hand side is the Euler characteristic `χ (S ^ (2 * n)) = 2`.

For `n = 1` this is the classical Gauss–Bonnet theorem `∫ K dA = 2 * π * χ` for the round
two-sphere. -/
theorem chern_gauss_bonnet (n : ℕ) (r : ℝ) (hr : 0 < r) :
    (1 / (2 * Real.pi) ^ n) * ((pfaffianConstCurv n / r ^ (2 * n)) * roundSphereVolume n r)
      = 2 := by
  rw [roundSphereVolume_eq n hr, pfaffianConstCurv]
  have hR : ((2 * n + 1)‼ : ℝ) * (2 ^ n * (n ! : ℝ)) = (2 * (n : ℝ) + 1) * ((2 * n)! : ℝ) := by
    have hnat : (2 * n + 1)‼ * (2 ^ n * n !) = (2 * n + 1) * (2 * n)! := by
      rw [doubleFactorial_odd_mul, Nat.factorial_succ]
    exact_mod_cast congrArg (fun k : ℕ => (k : ℝ)) hnat
  have hd : ((2 * n + 1)‼ : ℝ) > 0 := by positivity
  have hf : ((n ! : ℝ)) > 0 := by positivity
  have hpi : Real.pi > 0 := Real.pi_pos
  have hrp : r ^ (2 * n) > 0 := by positivity
  field_simp
  linear_combination (-(2 : ℝ) * Real.pi ^ n * 2 ^ n) * hR

/-- The classical Gauss–Bonnet theorem for the round two-sphere of radius `r`:
the total curvature `∫ K dA = (1 / r ^ 2) * area` equals `2 * π * χ` with `χ = 2`. -/
theorem gauss_bonnet_two_sphere (r : ℝ) (hr : 0 < r) :
    (1 / r ^ 2) * roundSphereVolume 1 r = 2 * Real.pi * 2 := by
  have h := chern_gauss_bonnet 1 r hr
  rw [pfaffianConstCurv] at h
  norm_num at h ⊢
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp at h
  rw [h]
  have hr2 : r ^ 2 ≠ 0 := by positivity
  field_simp

end Math2

