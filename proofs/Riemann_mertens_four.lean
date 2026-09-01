/-
# Det Eq Mertens 4
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_4
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

namespace Riemann
namespace Redheffer

/-- The 4×4 Redheffer matrix: `R i j = 1` if `j = 0` or `(i+1) ∣ (j+1)`, else `0`. -/
def R4 : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i j => if (j : ℕ) = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- The Mertens function `M(n) = ∑_{k=1}^{n} μ(k)`. -/
def mertens (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.moebius k

/-- `μ(4) = 0`, since `4` is not squarefree. -/
private lemma moebius_four : ArithmeticFunction.moebius 4 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro h
  have := h 2 (by norm_num)
  simp at this

/-- `M(4) = μ(1) + μ(2) + μ(3) + μ(4) = 1 - 1 - 1 + 0 = -1`. -/
lemma mertens_four : mertens 4 = -1 := by
  have hIcc : Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by decide
  rw [mertens, hIcc]
  norm_num [ArithmeticFunction.moebius_apply_prime, Nat.prime_two, Nat.prime_three, moebius_four]

/-- The determinant of the 4×4 Redheffer matrix equals the Mertens function `M(4) = -1`. -/
theorem det_eq_mertens_4 : R4.det = mertens 4 ∧ R4.det = -1 := by
  have hdet : R4.det = -1 := by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, R4, Matrix.submatrix, Fin.succAbove]
  exact ⟨hdet.trans mertens_four.symm, hdet⟩

end Redheffer
end Riemann

