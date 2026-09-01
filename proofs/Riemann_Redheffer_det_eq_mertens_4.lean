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

namespace Riemann
namespace Redheffer

/-- The 4×4 Redheffer matrix: `R i j = 1` if `j = 0` or `(i+1) ∣ (j+1)`, else `0`. -/
def R : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i j => if j = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- The Mertens function `M(n) = ∑_{k=1}^{n} μ(k)`. -/
def mertens (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.moebius k

/-- The determinant of the 4×4 Redheffer matrix equals `M(4) = -1`. -/
theorem det_eq_mertens_4 : R.det = -1 ∧ R.det = mertens 4 := by
  have hdet : R.det = -1 := by
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, R, Matrix.submatrix, Fin.succAbove]
  have h2 : (ArithmeticFunction.moebius 2 : ℤ) = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have h3 : (ArithmeticFunction.moebius 3 : ℤ) = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_three
  have h4 : (ArithmeticFunction.moebius 4 : ℤ) = 0 := by
    apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
    decide
  refine ⟨hdet, ?_⟩
  rw [hdet, mertens]
  norm_num [Finset.sum_Icc_succ_top, h2, h3, h4]

end Redheffer
end Riemann

