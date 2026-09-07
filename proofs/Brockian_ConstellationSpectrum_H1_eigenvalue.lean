/-
  Brockian/ConstellationSpectrum.lean — Brick 5: the path-Hamiltonian operators
  H₁, H₂, H₃ and their EXACT characteristic polynomials / eigenvalues, giving the
  five-point spectral alphabet {2 − √2, 1, 2, 3, 2 + √2}.

  These are the genuine `Matrix` operators (diagonal 2, −1 across each path edge) over
  ℝ — the path-graph (Dirichlet) Laplacians of the 1-, 2-, and 3-vertex paths:

      H₁ = !![2]                H₂ = !![2,-1; -1,2]        H₃ = !![2,-1,0; -1,2,-1; 0,-1,2]

  Theorem 1 (load-bearing) computes each characteristic polynomial `M.charpoly =
  (charmatrix M).det` explicitly and shows it factors exactly:
      charpoly H₁ = X − 2
      charpoly H₂ = (X − 1)(X − 3)
      charpoly H₃ = (X − 2)(X² − 4X + 2)
  The 3×3 cofactor expansion is (X−2)[(X−2)²−1] − (X−2) = (X−2)³ − 2(X−2)
  = (X−2)((X−2)²−2) = (X−2)(X²−4X+2).

  Theorem 2 reads off the roots (the actual operator spectrum), including the two
  irrational H₃ eigenvalues 2 ± √2 via (√2)² = 2.  Theorem 3 collects the union of the
  three block spectra as the five-point alphabet.

  HONEST SCOPE: this proves the BLOCK spectra — the spectral *alphabet* carried by the
  path blocks H₁, H₂, H₃.  Assembling the full constellation/wheel operator as a
  block-diagonal sum (a permutation-similarity argument) is a SEPARATE gate and is NOT
  claimed here.

  Verification: no sorry / admit / axiom / native_decide.  Core Mathlib only.
-/
import Mathlib

namespace Brockian.ConstellationSpectrum

open Polynomial Matrix

/-! ### The path-graph Hamiltonians -/

/-- The 1-vertex path Hamiltonian (Dirichlet Laplacian): `!![2]`. -/
def H1 : Matrix (Fin 1) (Fin 1) ℝ := !![2]

/-- The 2-vertex path Hamiltonian: diagonal `2`, off-diagonal `−1`. -/
def H2 : Matrix (Fin 2) (Fin 2) ℝ := !![2, -1; -1, 2]

/-- The 3-vertex path Hamiltonian: diagonal `2`, `−1` across each path edge. -/
def H3 : Matrix (Fin 3) (Fin 3) ℝ := !![2, -1, 0; -1, 2, -1; 0, -1, 2]

/-! ### Theorem 1 — exact characteristic polynomials (the operator spectra) -/

theorem H1_charpoly : H1.charpoly = Polynomial.X - Polynomial.C 2 := by
  rw [Matrix.charpoly, Matrix.det_fin_one]
  simp only [Matrix.charmatrix_apply, Matrix.diagonal_apply, H1, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_fin_one, ↓reduceIte, map_ofNat]

theorem H2_charpoly :
    H2.charpoly = (Polynomial.X - Polynomial.C 1) * (Polynomial.X - Polynomial.C 3) := by
  rw [Matrix.charpoly, Matrix.det_fin_two]
  simp only [Matrix.charmatrix_apply, Matrix.diagonal_apply, H2, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
    Fin.reduceEq, ↓reduceIte, map_neg, map_one, map_ofNat, neg_zero, zero_sub]
  ring

theorem H3_charpoly :
    H3.charpoly =
      (Polynomial.X - Polynomial.C 2) *
        (Polynomial.X ^ 2 - Polynomial.C 4 * Polynomial.X + Polynomial.C 2) := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp only [Matrix.charmatrix_apply, Matrix.diagonal_apply, H3, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.head_fin_const, Fin.reduceEq, ↓reduceIte,
    map_neg, map_one, map_zero, map_ofNat, neg_zero, zero_sub, sub_zero]
  ring

/-! ### Theorem 2 — the eigenvalues (roots) are exactly the five-point alphabet -/

theorem H1_eigenvalue (x : ℝ) : H1.charpoly.eval x = 0 ↔ x = 2 := by
  rw [H1_charpoly]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [sub_eq_zero]

theorem H2_eigenvalues (x : ℝ) : H2.charpoly.eval x = 0 ↔ x = 1 ∨ x = 3 := by
  rw [H2_charpoly]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [mul_eq_zero, sub_eq_zero, sub_eq_zero]

theorem H3_eigenvalues (x : ℝ) :
    H3.charpoly.eval x = 0 ↔ x = 2 ∨ x = 2 - Real.sqrt 2 ∨ x = 2 + Real.sqrt 2 := by
  rw [H3_charpoly]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  -- goal: (x - 2) * (x ^ 2 - 4 * x + 2) = 0 ↔ …
  have hfac : x ^ 2 - 4 * x + 2
      = (x - (2 - Real.sqrt 2)) * (x - (2 + Real.sqrt 2)) := by
    have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
    linear_combination h2
  rw [hfac, mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero, sub_eq_zero]

/-! ### Theorem 3 — the spectral alphabet -/

/-- The five-point spectral alphabet: the union of the block spectra of H₁, H₂, H₃. -/
noncomputable def spectralAlphabet : Finset ℝ := {2 - Real.sqrt 2, 1, 2, 3, 2 + Real.sqrt 2}

/-- Every eigenvalue of any of the three path-Hamiltonian blocks lies in the
    five-point spectral alphabet `{2 − √2, 1, 2, 3, 2 + √2}`. -/
theorem eigenvalues_in_alphabet (x : ℝ)
    (hx : H1.charpoly.eval x = 0 ∨ H2.charpoly.eval x = 0 ∨ H3.charpoly.eval x = 0) :
    x ∈ spectralAlphabet := by
  simp only [spectralAlphabet, Finset.mem_insert, Finset.mem_singleton]
  rcases hx with h | h | h
  · rw [H1_eigenvalue] at h; tauto
  · rw [H2_eigenvalues] at h; tauto
  · rw [H3_eigenvalues] at h; tauto

end Brockian.ConstellationSpectrum
