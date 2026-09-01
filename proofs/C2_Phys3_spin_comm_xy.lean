import Mathlib
open Matrix
namespace C2.Phys3
def Sx : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]
def Sy : Matrix (Fin 2) (Fin 2) ℂ := !![0,-Complex.I;Complex.I,0]
def Sz : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,-1]

theorem spin_comm_xy : Sx * Sy - Sy * Sx = (2*Complex.I) • Sz := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Sx, Sy, Sz, Complex.ext_iff] <;> ring

theorem spin_sq_id : Sx*Sx = 1 ∧ Sy*Sy = 1 ∧ Sz*Sz = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Sx, Sy, Sz, ← Matrix.ext_iff, Matrix.one_apply, Complex.I_mul_I]

theorem spin_anticomm : Sx*Sy + Sy*Sx = 0 := by
  simp [Sx, Sy, ← Matrix.ext_iff]

end C2.Phys3

