import Mathlib
open Matrix
namespace C5.Ph6
def Sx : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]
def Sy : Matrix (Fin 2) (Fin 2) ℂ := !![0,-Complex.I;Complex.I,0]
def Sz : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,-1]

theorem spin_total_sq : Sx*Sx+Sy*Sy+Sz*Sz = (3:ℂ)•(1:Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Sx, Sy, Sz, Matrix.one_fin_two, Complex.I_mul_I] <;> ring

theorem sy_hermitian : Syᴴ = Sy := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Sy, Matrix.conjTranspose]

theorem sxyz_det : Sx.det = -1 := by
  simp [Sx, Matrix.det_fin_two_of]
end C5.Ph6

