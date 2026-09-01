/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Polynomial

/-- The adjacency matrix of the cycle graph `C₄` (over `ℝ`), written explicitly. -/
theorem adjMatrix_cycleGraph_four :
    ((SimpleGraph.cycleGraph 4).adjMatrix ℝ) = !![(0:ℝ),1,0,1; 1,0,1,0; 0,1,0,1; 1,0,1,0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SimpleGraph.adjMatrix, SimpleGraph.cycleGraph, SimpleGraph.circulantGraph,
      SimpleGraph.fromRel] <;> decide

/-- The characteristic matrix of the adjacency matrix of `C₄`. -/
theorem charmatrix_adjMatrix_cycleGraph_four :
    Matrix.charmatrix ((SimpleGraph.cycleGraph 4).adjMatrix ℝ) =
      !![X, -1, 0, -1; -1, X, -1, 0; (0:ℝ[X]), -1, X, -1; -1, 0, -1, X] := by
  rw [adjMatrix_cycleGraph_four]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.charmatrix]

/-- The characteristic polynomial of the adjacency matrix of `C₄` is `X⁴ - 4X²`. -/
theorem charpoly_adjMatrix_cycleGraph_four :
    ((SimpleGraph.cycleGraph 4).adjMatrix ℝ).charpoly = X ^ 4 - 4 * X ^ 2 := by
  rw [Matrix.charpoly, charmatrix_adjMatrix_cycleGraph_four]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove,
    show ((1 : Fin 3) < 2) from by decide]
  ring

/-- **Hückel theory for cyclobutadiene (C₄).**  The eigenvalues of the adjacency matrix of the
cycle graph `C₄` are exactly `2 cos (2πk/4)` for `k = 0, 1, 2, 3`, with multiplicity:  the
characteristic polynomial factors as `∏ k, (X - 2 cos (2πk/4))`. -/
theorem huckel_C4 :
    ((SimpleGraph.cycleGraph 4).adjMatrix ℝ).charpoly =
      ∏ k : Fin 4, (X - C (2 * Real.cos (2 * Real.pi * (k : ℕ) / 4))) := by
  rw [charpoly_adjMatrix_cycleGraph_four]
  have h0 : (2 : ℝ) * Real.pi * ((0 : Fin 4) : ℕ) / 4 = 0 := by norm_num
  have h1 : (2 : ℝ) * Real.pi * ((1 : Fin 4) : ℕ) / 4 = Real.pi / 2 := by
    norm_num; ring
  have h2 : (2 : ℝ) * Real.pi * ((2 : Fin 4) : ℕ) / 4 = Real.pi := by
    norm_num; ring
  have h3 : (2 : ℝ) * Real.pi * ((3 : Fin 4) : ℕ) / 4 = Real.pi + Real.pi / 2 := by
    norm_num; ring
  rw [Fin.prod_univ_four, h0, h1, h2, h3]
  rw [Real.cos_zero, Real.cos_pi_div_two, Real.cos_pi, Real.cos_add, Real.cos_pi_div_two,
    Real.sin_pi_div_two, Real.sin_pi]
  have hC : (C (2:ℝ) : ℝ[X]) = 2 := map_ofNat C 2
  norm_num [hC]
  ring

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

