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
open scoped Pointwise

set_option maxHeartbeats 2000000
set_option maxRecDepth 40000

namespace Riemann
namespace Redheffer

/-- The `6 × 6` Redheffer matrix: `R i j = 1` if `j = 0` or `(i+1) ∣ (j+1)`, and `0` otherwise. -/
def R6 : Matrix (Fin 6) (Fin 6) ℤ :=
  Matrix.of fun i j => if j = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- Explicit entries of the `6 × 6` Redheffer matrix. -/
theorem R6_eq :
    R6 = !![1, 1, 1, 1, 1, 1;
            1, 1, 0, 1, 0, 1;
            1, 0, 1, 0, 0, 1;
            1, 0, 0, 1, 0, 0;
            1, 0, 0, 0, 1, 0;
            1, 0, 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

/-- The determinant of the `6 × 6` Redheffer matrix equals the Mertens function `M(6) = -1`. -/
theorem det_eq_mertens_6 : R6.det = -1 := by
  rw [R6_eq]
  decide

end Redheffer
end Riemann

