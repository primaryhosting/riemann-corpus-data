/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Real Matrix

/-- Adjacency matrix of the cycle graph `C₃` (the Hückel matrix of cyclopropenyl in
units where `α = 0`, `β = 1`): every pair of distinct vertices is adjacent. -/
def C3adj : Matrix (Fin 3) (Fin 3) ℝ := fun i j => if i = j then 0 else 1

/-- The Hückel eigenvalues of the cyclopropenyl ring `C₃`: a real number `μ` is an
eigenvalue of the adjacency matrix of `C₃` (i.e. `det (A - μ • 1) = 0`) if and only if
`μ = 2 cos (2πk/3)` for some `k ∈ {0, 1, 2}`. -/
theorem huckel_C3 (μ : ℝ) :
    (C3adj - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 0 ↔
      ∃ k : Fin 3, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 3) := by
  have hdet : (C3adj - μ • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det
      = -((μ - 2) * (μ + 1) ^ 2) := by
    simp [Matrix.det_fin_three, C3adj, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Fin.ext_iff]
    ring
  have hc0 : (2 : ℝ) * Real.cos (2 * Real.pi * (0 : ℕ) / 3) = 2 := by
    norm_num
  have hc1 : (2 : ℝ) * Real.cos (2 * Real.pi * (1 : ℕ) / 3) = -1 := by
    have h : 2 * Real.pi * (1 : ℕ) / 3 = Real.pi - Real.pi / 3 := by push_cast; ring
    rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
    norm_num
  have hc2 : (2 : ℝ) * Real.cos (2 * Real.pi * (2 : ℕ) / 3) = -1 := by
    have h : 2 * Real.pi * (2 : ℕ) / 3 = Real.pi + Real.pi / 3 := by push_cast; ring
    rw [h, Real.cos_add, Real.cos_pi_div_three, Real.sin_pi_div_three]
    simp
  constructor
  · intro h
    rw [hdet] at h
    have h' : (μ - 2) * (μ + 1) ^ 2 = 0 := by linarith [h]
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact ⟨0, by rw [hc0]; linarith⟩
    · have : μ + 1 = 0 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
        exact this
      exact ⟨1, by rw [hc1]; linarith⟩
  · rintro ⟨k, hk⟩
    rw [hdet]
    fin_cases k
    · rw [hc0] at hk; rw [hk]; ring
    · rw [hc1] at hk; rw [hk]; ring
    · rw [hc2] at hk; rw [hk]; ring

end Chem

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

