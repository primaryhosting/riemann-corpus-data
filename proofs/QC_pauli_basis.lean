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

namespace QC

/-- The four Pauli matrices `I, X, Y, Z`, as a family indexed by `Fin 4`. -/
def pauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![1, 0; 0, 1]
  | 1 => !![0, 1; 1, 0]
  | 2 => !![0, -Complex.I; Complex.I, 0]
  | 3 => !![1, 0; 0, -1]

theorem pauli_linearIndependent : LinearIndependent ℂ pauli := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [Fin.sum_univ_four] at hg
  have h00 := congrFun (congrFun hg 0) 0
  have h01 := congrFun (congrFun hg 0) 1
  have h10 := congrFun (congrFun hg 1) 0
  have h11 := congrFun (congrFun hg 1) 1
  simp [pauli, Matrix.add_apply] at h00 h01 h10 h11
  have h0 : g 0 = 0 := by linear_combination (h00 + h11) / 2
  have h3 : g 3 = 0 := by linear_combination (h00 - h11) / 2
  have h1 : g 1 = 0 := by linear_combination (h01 + h10) / 2
  have h2 : g 2 = 0 := by
    have hI : g 2 * Complex.I = 0 := by linear_combination (h10 - h01) / 2
    simpa [Complex.I_ne_zero] using hI
  fin_cases i <;> assumption

theorem pauli_span : Submodule.span ℂ (Set.range pauli) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun M => ?_
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨![(M 0 0 + M 1 1) / 2, (M 0 1 + M 1 0) / 2,
      Complex.I * (M 0 1 - M 1 0) / 2, (M 0 0 - M 1 1) / 2], ?_⟩
  rw [Fin.sum_univ_four]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.add_apply] <;>
    field_simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring

/-- The Pauli matrices `I, X, Y, Z` as a basis of the space of `2 × 2` complex matrices. -/
noncomputable def pauliBasis : Module.Basis (Fin 4) ℂ (Matrix (Fin 2) (Fin 2) ℂ) :=
  Module.Basis.mk pauli_linearIndependent (by rw [pauli_span])

@[simp] theorem coe_pauliBasis : ⇑pauliBasis = pauli := by
  simp [pauliBasis]

/-- `{I, X, Y, Z}` is a basis of the `ℂ`-vector space of `2 × 2` complex matrices:
the family is linearly independent over `ℂ` and spans the whole space. -/
theorem pauli_basis :
    LinearIndependent ℂ pauli ∧ Submodule.span ℂ (Set.range pauli) = ⊤ :=
  ⟨pauli_linearIndependent, pauli_span⟩

end QC

