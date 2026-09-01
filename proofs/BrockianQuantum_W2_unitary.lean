import Mathlib
/-!
# Batch 8 — discrete/quantum Fourier transform (concrete 2- and 4-point). All TRUE; bare import Mathlib.
-/
namespace BrockianQuantum
open Matrix
/-- 2-point DFT (unnormalized) = √2 · Hadamard. -/
def W2 : Matrix (Fin 2) (Fin 2) ℂ := !![1,1; 1,-1]
/-- 4-point DFT, entries i^{jk}. -/
noncomputable def W4 : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,1,1,1; 1,Complex.I,-1,-Complex.I; 1,-1,1,-1; 1,-Complex.I,-1,Complex.I]
/-- DFT² parity-reversal support. -/
def P4 : Matrix (Fin 4) (Fin 4) ℂ := !![1,0,0,0; 0,0,0,1; 0,0,1,0; 0,1,0,0]

theorem W2_unitary : W2 * W2ᴴ = (2 : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [W2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;> norm_num
theorem W2_sq : W2 * W2 = (2 : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [W2, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
theorem W2_det : W2.det = -2 := by
  simp [W2, Matrix.det_fin_two_of]
  ring
theorem W4_symmetric : W4ᵀ = W4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [W4, Matrix.transpose_apply]
theorem W4_row0 : ∀ k, W4 0 k = 1 := by
  intro k
  fin_cases k <;> simp [W4]
theorem W4_unitary : W4 * W4ᴴ = (4 : ℂ) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [W4, Matrix.mul_apply, Fin.sum_univ_four, Matrix.conjTranspose_apply,
      Complex.ext_iff] <;> ring
theorem W4_sq_reversal : W4 * W4 = (4 : ℂ) • P4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [W4, P4, Matrix.mul_apply, Fin.sum_univ_four, Complex.ext_iff] <;> ring
end BrockianQuantum

