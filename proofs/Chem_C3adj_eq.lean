/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
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

namespace Chem

open Polynomial

/-- The Hückel (adjacency) matrix of the cycle graph `C₃`: the π-system connectivity
matrix of a three-membered carbon ring, in units where the Coulomb integral is `α = 0`
and the resonance integral is `β = 1`. -/
noncomputable def C3adj : Matrix (Fin 3) (Fin 3) ℝ :=
  (SimpleGraph.cycleGraph 3).adjMatrix ℝ

/-- Explicit entries of the `C₃` adjacency matrix. -/
lemma C3adj_eq : C3adj = Matrix.of ![![0, 1, 1], ![1, 0, 1], ![1, 1, 0]] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C3adj, SimpleGraph.adjMatrix, SimpleGraph.cycleGraph] <;> decide

/-- The Hückel level `2 cos(2πk/3)` for `k = 0` equals `2`. -/
lemma huckel_val_zero : 2 * Real.cos (2 * Real.pi * (0 : ℕ) / 3) = 2 := by
  norm_num

/-- The Hückel level `2 cos(2πk/3)` for `k = 1` equals `-1`. -/
lemma huckel_val_one : 2 * Real.cos (2 * Real.pi * (1 : ℕ) / 3) = -1 := by
  have h : 2 * Real.pi * ((1 : ℕ) : ℝ) / 3 = Real.pi - Real.pi / 3 := by
    push_cast; ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

/-- The Hückel level `2 cos(2πk/3)` for `k = 2` equals `-1`. -/
lemma huckel_val_two : 2 * Real.cos (2 * Real.pi * (2 : ℕ) / 3) = -1 := by
  have h : 2 * Real.pi * ((2 : ℕ) : ℝ) / 3 = Real.pi + Real.pi / 3 := by
    push_cast; ring
  rw [h, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
  norm_num

/-- The characteristic polynomial of the `C₃` adjacency matrix is `X³ - 3X - 2`. -/
lemma C3adj_charpoly : C3adj.charpoly = X ^ 3 - 3 * X - 2 := by
  rw [C3adj_eq]
  simp [Matrix.charpoly, Matrix.det_fin_three, Matrix.charmatrix]
  ring

/-- The product of the linear factors `X - 2cos(2πk/3)` over `k = 0, 1, 2`. -/
lemma C3_spectral_prod :
    (∏ k ∈ Finset.range 3, (X - C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 3))))
      = X ^ 3 - 3 * X - 2 := by
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_zero, huckel_val_zero, huckel_val_one, huckel_val_two]
  simp [Polynomial.C_neg, map_ofNat]
  ring

/-- Multiplying a vector by the scalar matrix `μ • 1` is scalar multiplication by `μ`. -/
lemma scalar_mulVec (μ : ℝ) (v : Fin 3 → ℝ) :
    (Matrix.scalar (Fin 3) μ).mulVec v = μ • v := by
  have h : Matrix.scalar (Fin 3) μ = μ • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j; simp [Matrix.scalar, Matrix.one_apply, Matrix.diagonal_apply]
  rw [h, Matrix.smul_mulVec, Matrix.one_mulVec]

/-- `μ` is an eigenvalue of a `3 × 3` real matrix iff `μ • 1 - A` is singular. -/
lemma eigen_iff_det (A : Matrix (Fin 3) (Fin 3) ℝ) (μ : ℝ) :
    (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ A.mulVec v = μ • v) ↔
      (Matrix.scalar (Fin 3) μ - A).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, hAv⟩
    exact ⟨v, hv, by rw [Matrix.sub_mulVec, hAv, scalar_mulVec, sub_self]⟩
  · rintro ⟨v, hv, hAv⟩
    rw [Matrix.sub_mulVec, sub_eq_zero, scalar_mulVec] at hAv
    exact ⟨v, hv, hAv.symm⟩

/--
**Hückel theory for the cyclopropenyl π-system (`C₃`).**

The adjacency (Hückel) matrix of the cycle graph `C₃` has characteristic polynomial
`∏_{k=0}^{2} (X - 2cos(2πk/3))`, and a real number `μ` is an eigenvalue of that matrix
precisely when `μ = 2cos(2πk/3)` for some `k ∈ {0, 1, 2}`.

Numerically the spectrum is `{2, -1, -1}`: one bonding level at `α + 2β` and a doubly
degenerate antibonding level at `α - β`.
-/
theorem huckel_C3 :
    C3adj.charpoly
        = ∏ k ∈ Finset.range 3, (X - C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 3))) ∧
      ∀ μ : ℝ, (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ C3adj.mulVec v = μ • v) ↔
        ∃ k ∈ Finset.range 3, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 3) := by
  refine ⟨by rw [C3adj_charpoly, C3_spectral_prod], fun μ => ?_⟩
  rw [eigen_iff_det, ← Matrix.eval_charpoly, C3adj_charpoly]
  have hfac : (X ^ 3 - 3 * X - 2 : ℝ[X]).eval μ = (μ - 2) * (μ + 1) ^ 2 := by
    simp only [eval_sub, eval_pow, eval_X, eval_mul, eval_ofNat]
    ring
  rw [hfac]
  simp only [Finset.mem_range]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact ⟨0, by norm_num, by rw [huckel_val_zero]; linarith⟩
    · have h3 : μ + 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
      exact ⟨1, by norm_num, by rw [huckel_val_one]; linarith⟩
  · rintro ⟨k, hk3, hk⟩
    interval_cases k
    · rw [huckel_val_zero] at hk; rw [hk]; ring
    · rw [huckel_val_one] at hk; rw [hk]; ring
    · rw [huckel_val_two] at hk; rw [hk]; ring

end Chem

