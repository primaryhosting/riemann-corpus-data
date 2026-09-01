import Mathlib
/-!
# Batch 5 — Bell states as stabilizer eigenvectors. All TRUE; bare `import Mathlib`.
Basis order |00>,|01>,|10>,|11> = 0,1,2,3.  XX = X⊗X, ZZ = Z⊗Z.
-/
namespace BrockianQuantum
open Matrix
noncomputable def c : ℂ := (Real.sqrt 2 : ℂ)⁻¹
def XX : Matrix (Fin 4) (Fin 4) ℂ := !![0,0,0,1; 0,0,1,0; 0,1,0,0; 1,0,0,0]
def ZZ : Matrix (Fin 4) (Fin 4) ℂ := !![1,0,0,0; 0,-1,0,0; 0,0,-1,0; 0,0,0,1]
noncomputable def phiP : Fin 4 → ℂ := ![c, 0, 0, c]
noncomputable def phiM : Fin 4 → ℂ := ![c, 0, 0, -c]
noncomputable def psiP : Fin 4 → ℂ := ![0, c, c, 0]
noncomputable def psiM : Fin 4 → ℂ := ![0, c, -c, 0]

theorem phiP_XX_eigen : XX.mulVec phiP = phiP := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, XX, phiP, dotProduct, Fin.sum_univ_four]

theorem phiP_ZZ_eigen : ZZ.mulVec phiP = phiP := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, ZZ, phiP, dotProduct, Fin.sum_univ_four]

theorem psiP_XX_eigen : XX.mulVec psiP = psiP := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, XX, psiP, dotProduct, Fin.sum_univ_four]

theorem phiM_ZZ_eigen : ZZ.mulVec phiM = phiM := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, ZZ, phiM, dotProduct, Fin.sum_univ_four]

theorem psiM_ZZ_eigen : ZZ.mulVec psiM = -psiM := by
  funext i
  fin_cases i <;> simp [Matrix.mulVec, ZZ, psiM, dotProduct, Fin.sum_univ_four]

theorem phiP_normalized : ∑ i, Complex.normSq (phiP i) = 1 := by
  have hc : Complex.normSq c = 1 / 2 := by simp [c]
  simp [Fin.sum_univ_four, phiP, hc]
  norm_num

theorem phiP_psiP_orthogonal : ∑ i, (starRingEnd ℂ) (phiP i) * psiP i = 0 := by
  simp [Fin.sum_univ_four, phiP, psiP]

end BrockianQuantum

