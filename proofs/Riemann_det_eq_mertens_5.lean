import Mathlib

/-!
# Det Eq Mertens 5
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_5
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

namespace Riemann
namespace Redheffer

/-- The `5 × 5` Redheffer matrix over `ℤ` (0-indexed): the entry `(i, j)` is `1`
when `j = 0` or `(i+1) ∣ (j+1)`, and `0` otherwise. -/
def R : Matrix (Fin 5) (Fin 5) ℤ :=
  Matrix.of fun i j => if j = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- The determinant of the `5 × 5` Redheffer matrix equals the Mertens function
`M(5) = μ(1) + μ(2) + μ(3) + μ(4) + μ(5) = 1 - 1 - 1 + 0 - 1 = -2`. -/
theorem det_eq_mertens_5 : R.det = -2 := by
  simp only [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.submatrix_apply, R, Matrix.of_apply, Fin.succAbove]
  norm_num [Fin.lt_def]
  decide

/-- The Mertens function value `M(5)`, written out as the sum of `μ(n)` for `n ≤ 5`. -/
theorem mertens_5_value :
    (∑ n ∈ Finset.Icc 1 5, (ArithmeticFunction.moebius n : ℤ)) = -2 := by
  rw [show Finset.Icc 1 5 = ({1, 2, 3, 4, 5} : Finset ℕ) by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two,
    ArithmeticFunction.moebius_apply_prime Nat.prime_three,
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      (by simp [Nat.squarefree_iff_prime_squarefree]; exact ⟨2, Nat.prime_two, by norm_num⟩),
    ArithmeticFunction.moebius_apply_prime (by norm_num)]
  norm_num

/-- `det R` equals the Mertens function `M(5)`. -/
theorem det_eq_mertens_sum :
    R.det = ∑ n ∈ Finset.Icc 1 5, (ArithmeticFunction.moebius n : ℤ) := by
  rw [det_eq_mertens_5, mertens_5_value]

end Redheffer
end Riemann

