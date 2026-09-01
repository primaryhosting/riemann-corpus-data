import Mathlib

/-!
# Det Eq Mertens 4
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_4
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

set_option grind.warning false

namespace Riemann.Redheffer

/-- The `4 × 4` Redheffer matrix: `R i j = 1` if `j = 0` or `(i+1) ∣ (j+1)`,
and `R i j = 0` otherwise (indices `i j : Fin 4` viewed as `0,1,2,3`). -/
def R : Matrix (Fin 4) (Fin 4) ℤ :=
  fun i j => if j = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- The Mertens function value `M(4) = μ(1) + μ(2) + μ(3) + μ(4) = 1 - 1 - 1 + 0 = -1`. -/
theorem mertens_four : ∑ n ∈ Finset.Icc 1 4, (ArithmeticFunction.moebius n : ℤ) = -1 := by
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) from rfl]
  norm_num [ArithmeticFunction.moebius_apply_prime, ArithmeticFunction.moebius_apply_one]
  decide

/-- The determinant of the `4 × 4` Redheffer matrix equals `M(4) = -1`. -/
theorem det_eq_mertens_4 : R.det = -1 := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, R, Matrix.submatrix]
  decide

/-- Combined statement: `det R = M(4) = μ(1) + μ(2) + μ(3) + μ(4)`. -/
theorem det_eq_sum_moebius :
    R.det = ∑ n ∈ Finset.Icc 1 4, (ArithmeticFunction.moebius n : ℤ) := by
  rw [det_eq_mertens_4, mertens_four]

end Riemann.Redheffer

