/-
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Hückel theory for `C₉`

The Hückel matrix of the cycle `C₉` (in units where the Coulomb integral is `0` and the
resonance integral is `1`) is the adjacency matrix of `SimpleGraph.cycleGraph 9`.
This file diagonalizes it by the discrete Fourier transform (a Vandermonde matrix built from
a primitive ninth root of unity) and computes its characteristic polynomial and spectrum:
the eigenvalues are `2 cos (2πk/9)`, `k = 0, …, 8`.
-/

open Matrix Polynomial SimpleGraph

namespace Chem

/-- A primitive ninth root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 9)

lemma zeta_primitive : IsPrimitiveRoot zeta 9 := by
  have := Complex.isPrimitiveRoot_exp 9 (by norm_num)
  simpa [zeta] using this

lemma zeta_pow_nine : zeta ^ 9 = 1 := zeta_primitive.pow_eq_one

lemma zeta_pow_congr {m n : ℕ} (h : m % 9 = n % 9) : zeta ^ m = zeta ^ n := by
  conv_lhs => rw [← Nat.div_add_mod m 9]
  conv_rhs => rw [← Nat.div_add_mod n 9]
  rw [pow_add, pow_add, pow_mul, pow_mul, zeta_pow_nine, one_pow, one_pow, h]

/-- The Hückel (adjacency) matrix of the cycle graph `C₉`. -/
noncomputable def A9 : Matrix (Fin 9) (Fin 9) ℂ := (cycleGraph 9).adjMatrix ℂ

/-- The discrete Fourier (Vandermonde) matrix built from the powers of `zeta`. -/
noncomputable def F9 : Matrix (Fin 9) (Fin 9) ℂ :=
  Matrix.vandermonde (fun i : Fin 9 => zeta ^ (i : ℕ))

/-- The `k`-th Hückel eigenvalue of `C₉`. -/
noncomputable def lam (k : Fin 9) : ℂ := 2 * Real.cos (2 * Real.pi * (k : ℕ) / 9)

lemma zeta_pow_eq_exp (m : ℕ) :
    zeta ^ m = Complex.exp (((2 * Real.pi * m / 9 : ℝ) : ℂ) * Complex.I) := by
  rw [zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma lam_eq (k : Fin 9) : lam k = zeta ^ (k : ℕ) + zeta ^ (8 * (k : ℕ)) := by
  have h1 : zeta ^ (8 * (k : ℕ)) * zeta ^ (k : ℕ) = 1 := by
    rw [← pow_add]
    have h : 8 * (k : ℕ) + (k : ℕ) = 9 * (k : ℕ) := by ring
    rw [h, pow_mul, zeta_pow_nine, one_pow]
  have h2 : zeta ^ (8 * (k : ℕ)) = (zeta ^ (k : ℕ))⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [h2, zeta_pow_eq_exp, ← Complex.exp_neg, lam, Complex.ofReal_cos, Complex.two_cos]
  push_cast
  ring_nf

lemma F9_apply (i j : Fin 9) : F9 i j = zeta ^ ((i : ℕ) * (j : ℕ)) := by
  simp [F9, Matrix.vandermonde, pow_mul]

lemma shift_mod (a b c : ℕ) : ((a + c) % 9 * b) % 9 = (a * b + c * b) % 9 := by
  simp [Nat.add_mul]

lemma fin9_sub_one (i : Fin 9) : i - 1 = i + 8 := by revert i; decide

lemma fin9_pair_ne (i : Fin 9) : i - 1 ≠ i + 1 := by revert i; decide

/-- The Fourier matrix diagonalizes the Hückel matrix of `C₉`. -/
lemma A9_mul_F9 : A9 * F9 = F9 * Matrix.diagonal lam := by
  ext i j
  have hmv : (A9 * F9) i j = (A9 *ᵥ (fun l => F9 l j)) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hmv, A9, SimpleGraph.adjMatrix_mulVec_apply,
    SimpleGraph.cycleGraph_neighborFinset (n := 7) (v := i),
    Finset.sum_pair (fin9_pair_ne i),
    Matrix.mul_diagonal, F9_apply, F9_apply, F9_apply, lam_eq, mul_add, ← pow_add, ← pow_add,
    fin9_sub_one, add_comm (zeta ^ ((i : ℕ) * (j : ℕ) + (j : ℕ)))]
  congr 1
  · exact zeta_pow_congr (by rw [Fin.val_add]; simpa using shift_mod i j 8)
  · exact zeta_pow_congr (by rw [Fin.val_add]; simpa using shift_mod i j 1)

lemma F9_det_ne_zero : F9.det ≠ 0 := by
  rw [F9, Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  exact Fin.ext (zeta_primitive.pow_inj a.isLt b.isLt hab)

/-- The characteristic polynomial of the Hückel matrix of `C₉` factors with roots
`2 cos (2πk/9)`. -/
theorem huckel_C9_charpoly : A9.charpoly = ∏ k : Fin 9, (X - C (lam k)) := by
  have hu : IsUnit F9.det := isUnit_iff_ne_zero.mpr F9_det_ne_zero
  have hinv : F9⁻¹ * F9 = 1 := Matrix.nonsing_inv_mul _ hu
  have hA : A9 = F9 * (Matrix.diagonal lam * F9⁻¹) := by
    rw [← mul_assoc, ← A9_mul_F9, mul_assoc, Matrix.mul_nonsing_inv _ hu, mul_one]
  rw [hA, Matrix.charpoly_mul_comm, mul_assoc, hinv, mul_one, Matrix.charpoly_diagonal]

/-- **Hückel theory for `C₉`**: the adjacency (Hückel) eigenvalues of the cycle graph `C₉`
are exactly the numbers `2 cos (2πk/9)` for `k = 0, …, 8`. -/
theorem huckel_C9 :
    spectrum ℂ ((cycleGraph 9).adjMatrix ℂ) =
      {μ : ℂ | ∃ k : Fin 9, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 9)} := by
  ext μ
  rw [Set.mem_setOf_eq, show (cycleGraph 9).adjMatrix ℂ = A9 from rfl,
    Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C9_charpoly]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ,
    true_and, sub_eq_zero, lam]

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

