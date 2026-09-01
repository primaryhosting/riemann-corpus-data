import Mathlib
open Matrix
namespace C4.Phys5
def Sx : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;1,0]
def Sy : Matrix (Fin 2) (Fin 2) ℂ := !![0,-Complex.I;Complex.I,0]
def Sz : Matrix (Fin 2) (Fin 2) ℂ := !![1,0;0,-1]

theorem comm_yz : Sy*Sz - Sz*Sy = (2*Complex.I) • Sx := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Sx, Sy, Sz] <;> ring

theorem comm_zx : Sz*Sx - Sx*Sz = (2*Complex.I) • Sy := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Sx, Sy, Sz] <;> ring_nf <;> simp [Complex.I_sq]

theorem pauli_sum_sq : Sx*Sx + Sy*Sy + Sz*Sz = (3:ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Sx, Sy, Sz, Complex.I_mul_I] <;> norm_num
end C4.Phys5

