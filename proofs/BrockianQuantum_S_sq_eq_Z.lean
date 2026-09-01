import Mathlib
/-!
# Batch 3 — phase gates S, T (Clifford+T). All TRUE; bare `import Mathlib`.
-/
namespace BrockianQuantum
open Matrix
def PX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
noncomputable def PY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def PZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
/-- Phase gate S = diag(1, i). -/ noncomputable def S : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, Complex.I]
/-- T gate = diag(1, e^{iπ/4}). -/ noncomputable def T : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, Complex.exp (Complex.I * Real.pi / 4)]

theorem S_sq_eq_Z : S * S = PZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S, PZ, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem S_pow_four : S ^ 4 = 1 := by
  have h : S ^ 4 = (S * S) * (S * S) := by noncomm_ring
  rw [h, S_sq_eq_Z]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PZ, Matrix.mul_apply, Fin.sum_univ_two]

theorem S_unitary : S * Sᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_mul_I]

theorem T_sq_eq_S : T * T = S := by
  have h : Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4)
      = Complex.I := by
    rw [← Complex.exp_add]
    have e : Complex.I * (Real.pi : ℂ) / 4 + Complex.I * (Real.pi : ℂ) / 4
        = (Real.pi / 2 : ℝ) * Complex.I := by push_cast; ring
    rw [e, Complex.exp_mul_I]
    simp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T, S, Matrix.mul_apply, Fin.sum_univ_two, h]

theorem T_pow_eight : T ^ 8 = 1 := by
  have h : T ^ 8 = (T * T) ^ 4 := by noncomm_ring
  rw [h, T_sq_eq_S, S_pow_four]

theorem T_unitary : T * Tᴴ = 1 := by
  have h : Complex.exp (Complex.I * Real.pi / 4) *
      (starRingEnd ℂ) (Complex.exp (Complex.I * Real.pi / 4)) = 1 := by
    rw [← Complex.exp_conj, ← Complex.exp_add]
    have e : Complex.I * (Real.pi : ℂ) / 4
        + (starRingEnd ℂ) (Complex.I * (Real.pi : ℂ) / 4) = 0 := by
      rw [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
      ring
    rw [e, Complex.exp_zero]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [T, Matrix.mul_apply, Fin.sum_univ_two, h]

theorem S_conj_X_eq_Y : S * PX * Sᴴ = PY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [S, PX, PY, Matrix.mul_apply, Fin.sum_univ_two]
end BrockianQuantum

