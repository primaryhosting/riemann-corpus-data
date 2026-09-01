import Mathlib
namespace C4.LA2
open Matrix
theorem transpose_mul {m n k : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin k) ℝ) :
    (A*B)ᵀ = Bᵀ * Aᵀ := Matrix.transpose_mul A B
theorem det_one {n : ℕ} : (1 : Matrix (Fin n) (Fin n) ℝ).det = 1 := Matrix.det_one
theorem inv_mul_cancel_mat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit A.det) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul A h
end C4.LA2

