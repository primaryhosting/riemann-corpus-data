import Mathlib
/-!
# Det Eq Mertens 6
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Riemann
namespace Redheffer

/-- The `6 × 6` Redheffer matrix: entry `(i, j)` is `1` when `j = 0` or
`(i+1) ∣ (j+1)` (using the natural-number values of the indices), and `0` otherwise. -/
def R6 : Matrix (Fin 6) (Fin 6) ℤ :=
  Matrix.of fun i j => if (j : ℕ) = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- The determinant of the `6 × 6` Redheffer matrix equals the Mertens function
`M(6) = -1`. -/
theorem det_eq_mertens_6 : R6.det = -1 := by
  simp [R6, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix,
    Fin.succAbove, Fin.lt_def]
  decide

end Redheffer
end Riemann

