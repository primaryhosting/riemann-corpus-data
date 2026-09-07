import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl,
with `α = 0`, `β = 1`): vertices `0,1,2,3,4` in a cycle, `A i j = 1` iff `i` and `j`
are adjacent along the cycle. -/
def C5adj : Matrix (Fin 5) (Fin 5) ℝ :=
  !![0, 1, 0, 0, 1;
     1, 0, 1, 0, 0;
     0, 1, 0, 1, 0;
     0, 0, 1, 0, 1;
     1, 0, 0, 1, 0]

lemma C5adj_apply_eq_one_iff (i j : Fin 5) :
    C5adj i j = 1 ↔ (j = i + 1 ∨ i = j + 1) := by
  fin_cases i <;> fin_cases j <;> simp [C5adj]

/-- The characteristic polynomial of the adjacency matrix of `C₅`. -/
lemma charpoly_C5adj : C5adj.charpoly = X ^ 5 - 5 * X ^ 3 + 5 * X - 2 := by
  simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.succAbove, Matrix.diagonal_apply, Matrix.submatrix_apply, C5adj]
  ring

lemma cos_two_pi_div_five : Real.cos (2 * π / 5) = (√5 - 1) / 4 := by
  have h : (2 : ℝ) * π / 5 = 2 * (π / 5) := by ring
  rw [h, Real.cos_two_mul, Real.cos_pi_div_five]
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  nlinarith [h5]

lemma cos_four_pi_div_five : Real.cos (4 * π / 5) = -(1 + √5) / 4 := by
  have h : (4 : ℝ) * π / 5 = π - π / 5 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_five]
  ring

lemma cos_six_pi_div_five : Real.cos (6 * π / 5) = -(1 + √5) / 4 := by
  have h : (6 : ℝ) * π / 5 = 2 * π - 4 * π / 5 := by ring
  rw [h, Real.cos_two_pi_sub, cos_four_pi_div_five]

lemma cos_eight_pi_div_five : Real.cos (8 * π / 5) = (√5 - 1) / 4 := by
  have h : (8 : ℝ) * π / 5 = 2 * π - 2 * π / 5 := by ring
  rw [h, Real.cos_two_pi_sub, cos_two_pi_div_five]

/-- The product of the linear factors `X - 2·cos(2πk/5)`, `k = 0,…,4`, is exactly the
characteristic polynomial of `C₅`. -/
lemma prod_factors_eq :
    (∏ k : Fin 5, (X - C (2 * Real.cos (2 * π * (k : ℕ) / 5))) : ℝ[X])
      = X ^ 5 - 5 * X ^ 3 + 5 * X - 2 := by
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  refine Polynomial.funext fun x => ?_
  have e0 : (2 : ℝ) * π * ((0 : Fin 5) : ℕ) / 5 = 0 := by norm_num
  have e1 : (2 : ℝ) * π * ((1 : Fin 5) : ℕ) / 5 = 2 * π / 5 := by norm_num
  have e2 : (2 : ℝ) * π * ((2 : Fin 5) : ℕ) / 5 = 4 * π / 5 := by
    show (2 : ℝ) * π * ((2 : ℕ) : ℝ) / 5 = 4 * π / 5
    push_cast; ring
  have e3 : (2 : ℝ) * π * ((3 : Fin 5) : ℕ) / 5 = 6 * π / 5 := by
    show (2 : ℝ) * π * ((3 : ℕ) : ℝ) / 5 = 6 * π / 5
    push_cast; ring
  have e4 : (2 : ℝ) * π * ((4 : Fin 5) : ℕ) / 5 = 8 * π / 5 := by
    show (2 : ℝ) * π * ((4 : ℕ) : ℝ) / 5 = 8 * π / 5
    push_cast; ring
  simp only [Fin.prod_univ_five, eval_mul, eval_sub, eval_add, eval_pow, eval_X, eval_C,
    eval_ofNat, e0, e1, e2, e3, e4, cos_two_pi_div_five, cos_four_pi_div_five,
    cos_six_pi_div_five, cos_eight_pi_div_five, Real.cos_zero]
  linear_combination ((x - 2) * (-(x ^ 2 + x - 1) / 2 + (5 - √5 ^ 2) / 16)
    + (√5 ^ 2 - 5) * (x - 2) / 8) * h5

/-- **Hückel theory for the cyclopentadienyl system.** The eigenvalues of the adjacency
matrix of the cycle graph `C₅` are exactly `2·cos(2πk/5)` for `k = 0, 1, 2, 3, 4`: the
characteristic polynomial factors into the corresponding linear factors. -/
theorem huckel_C5 :
    C5adj.charpoly = ∏ k : Fin 5, (X - C (2 * Real.cos (2 * π * (k : ℕ) / 5))) := by
  rw [charpoly_C5adj, prod_factors_eq]

/-- Consequence: each `2·cos(2πk/5)` is an eigenvalue of the adjacency matrix of `C₅`,
i.e. a root of its characteristic polynomial. -/
theorem huckel_C5_isRoot (k : Fin 5) :
    C5adj.charpoly.IsRoot (2 * Real.cos (2 * π * (k : ℕ) / 5)) := by
  rw [huckel_C5]
  simp only [IsRoot.def, eval_prod, Finset.prod_eq_zero_iff]
  exact ⟨k, Finset.mem_univ k, by simp⟩

/-- Consequence: the roots of the characteristic polynomial of `C₅` are precisely the
numbers `2·cos(2πk/5)`, `k = 0,…,4`. -/
theorem huckel_C5_roots_eq :
    C5adj.charpoly.roots = (Finset.univ : Finset (Fin 5)).val.map
      (fun k => 2 * Real.cos (2 * π * (k : ℕ) / 5)) := by
  have h : (∏ k : Fin 5, (X - C (2 * Real.cos (2 * π * (k : ℕ) / 5))) : ℝ[X])
      = (((Finset.univ : Finset (Fin 5)).val.map
            (fun k => 2 * Real.cos (2 * π * (k : ℕ) / 5))).map (fun a => X - C a)).prod := by
    rw [Finset.prod_eq_multiset_prod, Multiset.map_map]
    rfl
  rw [huckel_C5, h, Polynomial.roots_multiset_prod_X_sub_C]

/-- Consequence: for each `k`, the number `2·cos(2πk/5)` really is an eigenvalue of the
adjacency matrix of `C₅`, i.e. it admits a nonzero eigenvector. -/
theorem huckel_C5_hasEigenvector (k : Fin 5) :
    ∃ v : Fin 5 → ℝ, v ≠ 0 ∧
      C5adj.mulVec v = (2 * Real.cos (2 * π * (k : ℕ) / 5)) • v := by
  set t : ℝ := 2 * Real.cos (2 * π * (k : ℕ) / 5)
  have hdet : (Matrix.scalar (Fin 5) t - C5adj).det = 0 := by
    rw [← Matrix.eval_charpoly]
    exact huckel_C5_isRoot k
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  refine ⟨v, hv0, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at hv
  rw [← hv]
  funext i
  simp [Matrix.scalar, Matrix.mulVec_diagonal]

end Chem

