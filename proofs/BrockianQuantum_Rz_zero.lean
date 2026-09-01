import Mathlib
/-!
# Batch 15 — single-qubit Z-rotations Rz(θ) = diag(e^{-iθ/2}, e^{iθ/2}) in SU(2). All TRUE.
-/
namespace BrockianQuantum
open Matrix
noncomputable def Rz (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-Complex.I * t / 2), 0; 0, Complex.exp (Complex.I * t / 2)]

theorem Rz_zero : Rz 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rz]

theorem Rz_add (s t : ℝ) : Rz s * Rz t = Rz (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rz, Matrix.mul_apply, Fin.sum_univ_succ, ← Complex.exp_add] <;> ring_nf

theorem Rz_conj (t : ℝ) : (Rz t)ᴴ = Rz (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Rz, ← Complex.exp_conj, map_div₀, Complex.conj_I, map_ofNat]

theorem Rz_unitary (t : ℝ) : Rz t * (Rz t)ᴴ = 1 := by
  rw [Rz_conj, Rz_add]
  simp [Rz_zero]

theorem Rz_det (t : ℝ) : (Rz t).det = 1 := by
  simp [Rz, Matrix.det_fin_two_of, ← Complex.exp_add]
  ring_nf
  simp

theorem Rz_two_pi : Rz (2 * Real.pi) = -1 := by
  have h1 : Complex.exp (Complex.I * (Real.pi : ℂ)) = -1 := by
    rw [mul_comm]; exact Complex.exp_pi_mul_I
  have h2 : Complex.exp (-(Complex.I * (Real.pi : ℂ))) = -1 := by
    rw [Complex.exp_neg, h1]; norm_num
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rz] <;> ring_nf <;> simp [h1, h2]

theorem Rz_four_pi : Rz (4 * Real.pi) = 1 := by
  have h1 : Complex.exp (Complex.I * (Real.pi : ℂ) * 2) = 1 := by
    rw [mul_comm (Complex.I * (Real.pi : ℂ)) 2, ← mul_assoc, mul_comm (2 : ℂ) Complex.I,
      mul_assoc, mul_comm Complex.I]
    exact Complex.exp_two_pi_mul_I
  have h2 : Complex.exp (-(Complex.I * (Real.pi : ℂ) * 2)) = 1 := by
    rw [Complex.exp_neg, h1]; norm_num
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rz] <;> ring_nf <;> simp [h1, h2]
end BrockianQuantum

