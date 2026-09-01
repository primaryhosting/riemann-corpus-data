import Mathlib
open Matrix
namespace C4.QC6
noncomputable def T : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,Complex.exp (Complex.I*Real.pi/4)]
def S : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,Complex.I]

theorem T_sq_eq_S : T * T = S := by
  have h : Complex.exp (Complex.I*Real.pi/4) * Complex.exp (Complex.I*Real.pi/4)
      = Complex.I := by
    rw [← Complex.exp_add]
    have h2 : Complex.I*(Real.pi:ℂ)/4 + Complex.I*(Real.pi:ℂ)/4
        = ((Real.pi/2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h2, Complex.exp_mul_I]
    simp
  rw [T, S, Matrix.mul_fin_two]
  simp [h]

theorem S_sq_eq_Z : S * S = !![1,0;0,-1] := by
  rw [S, Matrix.mul_fin_two]
  simp [Complex.I_mul_I]

def X : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]

theorem X_hermitian : Xᴴ = X := by
  rw [X]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

end C4.QC6

