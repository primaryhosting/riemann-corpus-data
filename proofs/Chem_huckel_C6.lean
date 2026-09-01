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

namespace Chem

open Polynomial

/-- The Hückel matrix of benzene (in units where the Coulomb integral `α` is `0` and the
resonance integral `β` is `1`): the adjacency matrix of the cycle graph `C₆`. -/
noncomputable def C6adj : Matrix (Fin 6) (Fin 6) ℝ :=
  (SimpleGraph.cycleGraph 6).adjMatrix ℝ

/-- Explicit description of the adjacency matrix of `C₆`. -/
theorem C6adj_eq :
    C6adj = !![0, 1, 0, 0, 0, 1;
                1, 0, 1, 0, 0, 0;
                0, 1, 0, 1, 0, 0;
                0, 0, 1, 0, 1, 0;
                0, 0, 0, 1, 0, 1;
                1, 0, 0, 0, 1, 0] := by
  unfold C6adj
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SimpleGraph.adjMatrix_apply, Matrix.cons_val] <;> decide

/-- The characteristic polynomial of the adjacency matrix of `C₆`. -/
theorem C6adj_charpoly : C6adj.charpoly = X ^ 6 - 6 * X ^ 4 + 9 * X ^ 2 - 4 := by
  rw [C6adj_eq]
  simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, Fin.succAbove]
  ring

/-- The product `∏_{k=0}^{5} (X - 2·cos(2πk/6))` expanded. -/
theorem prod_cos_expand :
    ∏ k ∈ Finset.range 6, (X - C (2 * Real.cos (2 * Real.pi * k / 6))) =
      (X : ℝ[X]) ^ 6 - 6 * X ^ 4 + 9 * X ^ 2 - 4 := by
  have e0 : Real.cos (2 * Real.pi * (0 : ℕ) / 6) = 1 := by norm_num
  have e1 : Real.cos (2 * Real.pi * (1 : ℕ) / 6) = 1 / 2 := by
    rw [show (2 * Real.pi * ((1 : ℕ) : ℝ) / 6) = Real.pi / 3 by push_cast; ring,
      Real.cos_pi_div_three]
  have e2 : Real.cos (2 * Real.pi * (2 : ℕ) / 6) = -(1 / 2) := by
    rw [show (2 * Real.pi * ((2 : ℕ) : ℝ) / 6) = Real.pi - Real.pi / 3 by push_cast; ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  have e3 : Real.cos (2 * Real.pi * (3 : ℕ) / 6) = -1 := by
    rw [show (2 * Real.pi * ((3 : ℕ) : ℝ) / 6) = Real.pi by push_cast; ring, Real.cos_pi]
  have e4 : Real.cos (2 * Real.pi * (4 : ℕ) / 6) = -(1 / 2) := by
    rw [show (2 * Real.pi * ((4 : ℕ) : ℝ) / 6) = Real.pi + Real.pi / 3 by push_cast; ring,
      Real.cos_add, Real.cos_pi_div_three]
    simp
  have e5 : Real.cos (2 * Real.pi * (5 : ℕ) / 6) = 1 / 2 := by
    rw [show (2 * Real.pi * ((5 : ℕ) : ℝ) / 6) = 2 * Real.pi - Real.pi / 3 by push_cast; ring,
      Real.cos_sub, Real.cos_pi_div_three]
    simp
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
    Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_one, e0, e1, e2, e3, e4, e5]
  norm_num [Polynomial.C_neg, map_ofNat]
  ring

/-- **Hückel theory for benzene (`C₆`), characteristic polynomial form.**
The characteristic polynomial of the adjacency matrix of the cycle graph `C₆` factors as
`∏_{k=0}^{5} (X - 2·cos(2πk/6))`, i.e. the eigenvalues, with multiplicity, are
`2·cos(2πk/6)` for `k = 0, …, 5`. -/
theorem huckel_C6_charpoly :
    C6adj.charpoly = ∏ k ∈ Finset.range 6, (X - C (2 * Real.cos (2 * Real.pi * k / 6))) := by
  rw [C6adj_charpoly, prod_cos_expand]

/-- **Hückel theory for benzene (`C₆`).**
A real number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₆` (i.e. there is a
nonzero vector `v` with `A *ᵥ v = μ • v`) if and only if `μ = 2·cos(2πk/6)` for some
`k ∈ {0, 1, 2, 3, 4, 5}`. -/
theorem huckel_C6 (μ : ℝ) :
    (∃ v : Fin 6 → ℝ, v ≠ 0 ∧ C6adj.mulVec v = μ • v) ↔
      ∃ k : ℕ, k < 6 ∧ μ = 2 * Real.cos (2 * Real.pi * k / 6) := by
  have hstep : (∃ v : Fin 6 → ℝ, v ≠ 0 ∧ C6adj.mulVec v = μ • v) ↔
      (μ • (1 : Matrix (Fin 6) (Fin 6) ℝ) - C6adj).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro ⟨v, hv, hvA⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, hvA, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
    · rintro ⟨v, hv, hvA⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hvA
      exact hvA.symm
  have hdet : (μ • (1 : Matrix (Fin 6) (Fin 6) ℝ) - C6adj).det = C6adj.charpoly.eval μ := by
    rw [Matrix.eval_charpoly]
    congr 1
    ext i j
    simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.diagonal_apply]
  rw [hstep, hdet, huckel_C6_charpoly]
  rw [Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, hk, hk0⟩
    exact ⟨k, Finset.mem_range.mp hk, by linarith [sub_eq_zero.mp hk0]⟩
  · rintro ⟨k, hk, hk0⟩
    exact ⟨k, Finset.mem_range.mpr hk, by rw [hk0, sub_self]⟩

end Chem

