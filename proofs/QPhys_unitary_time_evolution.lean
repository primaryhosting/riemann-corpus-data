/-
# Unitary Time Evolution
Category: Quantum Physics
Target: QPhys.unitary_time_evolution
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QPhys

open NormedSpace

/-- The generator `-i H t / ℏ` of the time evolution is anti-Hermitian when `H` is Hermitian. -/
lemma conjTranspose_smul_eq_neg {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (hbar t : ℝ) :
    (((-Complex.I * (t / hbar)) • H)ᴴ) = -((-Complex.I * (t / hbar)) • H) := by
  rw [Matrix.conjTranspose_smul, hH.eq, ← neg_smul]
  congr 1
  simp [Complex.ext_iff]

/-- **Unitary time evolution.**  If `H` is a self-adjoint (Hermitian) Hamiltonian, then for every
real time `t` the propagator `U(t) = exp (-i H t / ℏ)` is a unitary matrix. -/
theorem unitary_time_evolution {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) (hbar t : ℝ) :
    exp ((-Complex.I * (t / hbar)) • H) ∈ Matrix.unitaryGroup n ℂ := by
  have hA := conjTranspose_smul_eq_neg H hH hbar t
  rw [Matrix.mem_unitaryGroup_iff, ← Matrix.exp_conjTranspose, hA,
    ← Matrix.exp_add_of_commute _ _ (by simp [Commute, SemiconjBy])]
  simp

end QPhys

