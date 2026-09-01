/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Matrix

namespace Chem

/-- The adjacency matrix (Hückel matrix with `α = 0`, `β = 1`) of the cycle graph `C₄`. -/
noncomputable def C4Adj : Matrix (Fin 4) (Fin 4) ℂ := (SimpleGraph.cycleGraph 4).adjMatrix ℂ

/-- The Hückel eigenvalue predicted for the `k`-th molecular orbital of `C₄`:
`2 cos (2πk/4)`. -/
noncomputable def cosEig (k : Fin 4) : ℂ := ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 4) : ℝ) : ℂ)

lemma C4Adj_eq : C4Adj = !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C4Adj, SimpleGraph.adjMatrix_apply, SimpleGraph.cycleGraph_adj] <;> decide

/-! ### The four Hückel eigenvalues -/

lemma cosEig_zero : cosEig 0 = 2 := by
  have h : (2 * Real.pi * ((0 : ℕ) : ℝ) / 4 : ℝ) = 0 := by push_cast; ring
  rw [cosEig, show ((0 : Fin 4) : ℕ) = 0 from rfl, h, Real.cos_zero]
  norm_num

lemma cosEig_one : cosEig 1 = 0 := by
  have h : (2 * Real.pi * ((1 : ℕ) : ℝ) / 4 : ℝ) = Real.pi / 2 := by push_cast; ring
  rw [cosEig, show ((1 : Fin 4) : ℕ) = 1 from rfl, h, Real.cos_pi_div_two]
  norm_num

lemma cosEig_two : cosEig 2 = -2 := by
  have h : (2 * Real.pi * ((2 : ℕ) : ℝ) / 4 : ℝ) = Real.pi := by push_cast; ring
  rw [cosEig, show ((2 : Fin 4) : ℕ) = 2 from rfl, h, Real.cos_pi]
  norm_num

lemma cosEig_three : cosEig 3 = 0 := by
  have h : (2 * Real.pi * ((3 : ℕ) : ℝ) / 4 : ℝ) = Real.pi + Real.pi / 2 := by push_cast; ring
  have c : Real.cos (Real.pi + Real.pi / 2) = 0 := by rw [Real.cos_add]; simp
  rw [cosEig, show ((3 : Fin 4) : ℕ) = 3 from rfl, h, c]
  norm_num

lemma range_cosEig : Set.range cosEig = {2, 0, -2} := by
  ext r
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k
    · exact Or.inl cosEig_zero
    · exact Or.inr (Or.inl cosEig_one)
    · exact Or.inr (Or.inr cosEig_two)
    · exact Or.inr (Or.inl cosEig_three)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, cosEig_zero⟩
    · exact ⟨1, cosEig_one⟩
    · exact ⟨2, cosEig_two⟩

/-! ### The characteristic determinant -/

set_option maxRecDepth 4000 in
lemma det_cycle_four {R : Type*} [CommRing R] (r : R) :
    (!![r, -1, 0, -1; -1, r, -1, 0; 0, -1, r, -1; -1, 0, -1, r] : Matrix (Fin 4) (Fin 4) R).det
      = r ^ 4 - 4 * r ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  ring

lemma mem_spectrum_iff_det_eq_zero (r : ℂ) :
    r ∈ spectrum ℂ C4Adj ↔ (r • (1 : Matrix (Fin 4) (Fin 4) ℂ) - C4Adj).det = 0 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_ne_iff,
    Algebra.algebraMap_eq_smul_one]

lemma resolvent_matrix (r : ℂ) :
    r • (1 : Matrix (Fin 4) (Fin 4) ℂ) - C4Adj =
      !![r, -1, 0, -1; -1, r, -1, 0; 0, -1, r, -1; -1, 0, -1, r] := by
  rw [C4Adj_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The spectrum of the adjacency matrix of `C₄` is `{2, 0, -2}`. -/
lemma spectrum_C4Adj : spectrum ℂ C4Adj = {2, 0, -2} := by
  ext r
  rw [mem_spectrum_iff_det_eq_zero, resolvent_matrix, det_cycle_four]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    have h' : r ^ 2 * ((r - 2) * (r + 2)) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact Or.inr (Or.inl (by simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1))
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact Or.inl (by linear_combination h2)
      · exact Or.inr (Or.inr (by linear_combination h2))
  · rintro (rfl | rfl | rfl) <;> ring

/-- **Hückel theory for cyclobutadiene `C₄`.**
The eigenvalues of the adjacency matrix of the cycle graph `C₄` are exactly
`2 cos (2πk/4)` for `k = 0, 1, 2, 3` (namely `2, 0, -2, 0`). -/
theorem huckel_C4 :
    spectrum ℂ ((SimpleGraph.cycleGraph 4).adjMatrix ℂ)
      = Set.range fun k : Fin 4 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 4) : ℝ) : ℂ) := by
  have : (fun k : Fin 4 => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 4) : ℝ) : ℂ)) = cosEig := rfl
  rw [this, range_cosEig, ← C4Adj, spectrum_C4Adj]

/-! ### The characteristic polynomial, which also records the multiplicities -/

lemma charmatrix_C4Adj :
    charmatrix C4Adj = !![Polynomial.X, -1, 0, -1; -1, Polynomial.X, -1, 0;
      0, -1, Polynomial.X, -1; -1, 0, -1, Polynomial.X] := by
  rw [C4Adj_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [charmatrix]

/-- The characteristic polynomial of the adjacency matrix of `C₄` factors as
`∏ k, (X - 2 cos (2πk/4))`; in particular the eigenvalue `0` is doubly degenerate. -/
theorem huckel_C4_charpoly :
    C4Adj.charpoly = ∏ k : Fin 4, (Polynomial.X - Polynomial.C (cosEig k)) := by
  rw [Matrix.charpoly, charmatrix_C4Adj, det_cycle_four, Fin.prod_univ_four,
    cosEig_zero, cosEig_one, cosEig_two, cosEig_three]
  simp only [map_zero, map_neg, map_ofNat, sub_zero, sub_neg_eq_add]
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

