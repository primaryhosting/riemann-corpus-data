/-
# Det Eq Mertens 5
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_5
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

namespace Riemann.Redheffer

/-- The `5 × 5` Redheffer matrix over `ℤ` (rows and columns indexed by `Fin 5`,
so entry `(i, j)` corresponds to the pair `(i+1, j+1)`):
the entry is `1` when `j = 0` (i.e. the first column) or when `i+1` divides `j+1`,
and `0` otherwise. -/
def R : Matrix (Fin 5) (Fin 5) ℤ :=
  fun i j => if j = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- The determinant of the `5 × 5` Redheffer matrix equals the Mertens function
`M(5) = μ(1) + μ(2) + μ(3) + μ(4) + μ(5) = 1 - 1 - 1 + 0 - 1 = -2`. -/
theorem det_eq_mertens_5 : Matrix.det R = -2 := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, R, Matrix.submatrix]
  decide

/-- The value `-2` above is indeed the Mertens function at `5`, i.e. the sum of the
Möbius function over `1, …, 5`. -/
theorem det_eq_sum_moebius :
    Matrix.det R = ∑ n ∈ Finset.Icc 1 5, ArithmeticFunction.moebius n := by
  have h4 : ArithmeticFunction.moebius 4 = 0 := by
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree]
    decide
  rw [det_eq_mertens_5, show (Finset.Icc 1 5) = ({1, 2, 3, 4, 5} : Finset ℕ) from rfl]
  norm_num [ArithmeticFunction.moebius_apply_of_squarefree,
    ArithmeticFunction.moebius_apply_prime, h4]

end Riemann.Redheffer

