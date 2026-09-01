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

open scoped Nat Real BigOperators
open MeasureTheory Metric Real

namespace Math2

/-! ## The Euler characteristic of an even-dimensional sphere

Mathlib does not (yet) compute the singular homology of spheres, so we take the Euler
characteristic of `Sᵈ` in its combinatorial form: `Sᵈ` is homeomorphic to the boundary
`∂Δ^{d+1}` of the standard `(d+1)`-simplex, which is a simplicial complex whose `k`-dimensional
faces are the `(k+1)`-element subsets of the `(d+2)`-element vertex set.  The Euler
characteristic is the alternating sum of the numbers of faces. -/

/-- The Euler characteristic of the `d`-dimensional sphere `Sᵈ`, computed from its standard
triangulation as the boundary of the `(d+1)`-simplex. -/
def eulerCharSphere (d : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (d + 1), (-1) ^ k * ((d + 2).choose (k + 1) : ℤ)

/-- `χ(Sᵈ) = 1 + (-1)ᵈ`. -/
lemma eulerCharSphere_eq (d : ℕ) : eulerCharSphere d = 1 + (-1) ^ d := by
  have h := @Int.alternating_sum_range_choose (d + 2)
  rw [if_neg (by omega), Finset.sum_range_succ'] at h
  simp only [pow_succ, Nat.choose_zero_right, pow_zero, one_mul, Nat.cast_one] at h
  rw [Finset.sum_range_succ] at h
  simp only [Nat.choose_self, Nat.cast_one, mul_one] at h
  have key : ∑ x ∈ Finset.range (d + 1), ((-1 : ℤ)) ^ x * -1 * ((d + 2).choose (x + 1) : ℤ)
      = - ∑ k ∈ Finset.range (d + 1), (-1 : ℤ) ^ k * ((d + 2).choose (k + 1) : ℤ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [key] at h
  unfold eulerCharSphere
  linear_combination -h

/-- `χ(S^{2n}) = 2`. -/
lemma eulerCharSphere_two_mul (n : ℕ) : eulerCharSphere (2 * n) = 2 := by
  rw [eulerCharSphere_eq, pow_mul]
  norm_num

/-! ## The Pfaffian curvature density of the round sphere -/

/-- The Chern–Gauss–Bonnet integrand of the unit round sphere `S^{2n}`.

For a closed oriented Riemannian `2n`-manifold the Chern–Gauss–Bonnet integrand is the
Pfaffian `Pf(Ω)` of the curvature `2`-form `Ω`.  For the unit round sphere the curvature form
in a local orthonormal frame is `Ω_{ij} = e_i ∧ e_j`, so `Pf(Ω)` is the constant multiple
`(2n)! / (2ⁿ n!)` of the Riemannian volume form. -/
noncomputable def pfaffianCurvatureDensity (n : ℕ) : ℝ :=
  ((2 * n)! : ℝ) / (2 ^ n * (n ! : ℝ))

/-- The Riemannian (surface) measure of the unit sphere `S^{2n} ⊆ ℝ^{2n+1}`, obtained from the
Lebesgue measure of the ambient space by the polar-coordinates decomposition. -/
noncomputable def sphereMeasure (n : ℕ) :
    Measure (sphere (0 : EuclideanSpace ℝ (Fin (2 * n + 1))) 1) :=
  (volume : Measure (EuclideanSpace ℝ (Fin (2 * n + 1)))).toSphere

/-- The total volume (surface area) of the unit sphere `S^{2n}` is `2^{2n+1} πⁿ n! / (2n)!`. -/
lemma sphereMeasure_real_univ (n : ℕ) :
    (sphereMeasure n).real Set.univ = 2 ^ (2 * n + 1) * π ^ n * (n ! : ℝ) / ((2 * n)! : ℝ) := by
  have hnatid : (2 * n + 1) * (2 * n)! = (2 * n + 1)‼ * (2 ^ n * n !) := by
    have h1 := Nat.factorial_eq_mul_doubleFactorial (2 * n)
    rw [Nat.doubleFactorial_two_mul n, Nat.factorial_succ] at h1
    exact h1
  have hnat : (2 * (n : ℝ) + 1) * ((2 * n)! : ℝ)
      = ((2 * n + 1)‼ : ℝ) * (2 ^ n * (n ! : ℝ)) := by
    have h := congrArg (Nat.cast (R := ℝ)) hnatid
    push_cast at h ⊢
    linarith [h]
  have hpi : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hdf : ((2 * n + 1)‼ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos (2 * n + 1)).ne'
  have hfac : ((2 * n)! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos (2 * n)).ne'
  rw [sphereMeasure, MeasureTheory.Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin,
    MeasureTheory.measureReal_def, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  rw [show (((2 * n + 1 : ℕ) : ℝ) / 2 + 1) = ((n + 1 : ℕ) : ℝ) + 1 / 2 from by push_cast; ring,
    Real.Gamma_nat_add_half, show 2 * (n + 1) - 1 = 2 * n + 1 from by omega,
    show √π ^ (2 * n + 1) = π ^ n * √π from by
      rw [pow_succ, pow_mul, Real.sq_sqrt Real.pi_pos.le],
    show ((2 * n + 1 : ℕ) : ℝ) = 2 * (n : ℝ) + 1 from by push_cast; ring]
  set A := ((2 * n + 1)‼ : ℝ)
  set B := ((2 * n)! : ℝ)
  set C := (n ! : ℝ)
  field_simp
  ring_nf
  linear_combination (2 : ℝ) ^ (n + 1) * hnat

/-! ## The Chern–Gauss–Bonnet theorem -/

/-- **Chern–Gauss–Bonnet** for the closed even-dimensional manifold `S^{2n}`:
the integral over the manifold of the Pfaffian of its curvature form, normalised by `(2π)ⁿ`,
equals the Euler characteristic of the manifold. -/
theorem chern_gauss_bonnet (n : ℕ) :
    ((2 * π) ^ n)⁻¹ *
        ∫ _x : sphere (0 : EuclideanSpace ℝ (Fin (2 * n + 1))) 1,
          pfaffianCurvatureDensity n ∂(sphereMeasure n)
      = (eulerCharSphere (2 * n) : ℝ) := by
  have hfac : ((2 * n)! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos (2 * n)).ne'
  have hnf : ((n)! : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [MeasureTheory.integral_const, sphereMeasure_real_univ, smul_eq_mul,
    pfaffianCurvatureDensity, eulerCharSphere_two_mul, mul_pow]
  push_cast
  field_simp
  ring

/-- The classical Gauss–Bonnet theorem in dimension two, as the case `n = 1` of
`Math2.chern_gauss_bonnet`: for the unit sphere `S²` the Gauss curvature is `1`, so
`∫_{S²} K dA = 4π = 2π · χ(S²)`. -/
theorem gauss_bonnet_sphere_two :
    (sphereMeasure 1).real Set.univ = 2 * π * (eulerCharSphere 2 : ℝ) := by
  rw [sphereMeasure_real_univ, eulerCharSphere_two_mul 1]
  norm_num
  ring

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

