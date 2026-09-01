import Mathlib

/-!
# Det Eq Mertens 4
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Redheffer

open ArithmeticFunction

/-- The 4×4 Redheffer matrix: `R i j = 1` if `j = 0` (first column) or if
`(i+1) ∣ (j+1)` (divisibility of the 1-based indices), and `0` otherwise. -/
def R : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i j => if j = 0 ∨ (i.val + 1) ∣ (j.val + 1) then 1 else 0

/-- Explicit entries of the 4×4 Redheffer matrix. -/
theorem R_eq : R = !![1, 1, 1, 1; 1, 1, 0, 1; 1, 0, 1, 0; 1, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [R]

/-- The determinant of the 4×4 Redheffer matrix equals the Mertens function
`M(4) = μ(1) + μ(2) + μ(3) + μ(4) = 1 - 1 - 1 + 0 = -1`. -/
theorem det_eq_mertens_4 : R.det = -1 := by
  rw [R_eq]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  decide

/-- The value `-1` is indeed the Mertens function `M(4) = ∑_{n ≤ 4} μ(n)`. -/
theorem sum_moebius_Icc_four : ∑ n ∈ Finset.Icc 1 4, (moebius n : ℤ) = -1 := by
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [show (moebius 2 : ℤ) = -1 from moebius_apply_prime (by norm_num),
      show (moebius 3 : ℤ) = -1 from moebius_apply_prime (by norm_num),
      show (moebius 4 : ℤ) = 0 by decide, moebius_apply_one]
  norm_num

/-- The determinant of the 4×4 Redheffer matrix is the sum of the values of the
Möbius function at `1, 2, 3, 4`, i.e. the Mertens function `M(4)`. -/
theorem det_eq_sum_moebius :
    R.det = ∑ n ∈ Finset.Icc 1 4, (moebius n : ℤ) := by
  rw [det_eq_mertens_4, sum_moebius_Icc_four]

end Riemann.Redheffer

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

