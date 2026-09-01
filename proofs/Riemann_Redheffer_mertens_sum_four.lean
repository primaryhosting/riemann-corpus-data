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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false


namespace Riemann.Redheffer

/-- The 4×4 Redheffer matrix: `R i j = 1` if `j = 0` or `(i+1) ∣ (j+1)`, else `0`. -/
def R4 : Matrix (Fin 4) (Fin 4) ℤ :=
  fun i j => if (j : ℕ) = 0 ∨ ((i : ℕ) + 1) ∣ ((j : ℕ) + 1) then 1 else 0

/-- The Mertens function at 4: `μ 1 + μ 2 + μ 3 + μ 4 = 1 - 1 - 1 + 0 = -1`. -/
theorem mertens_sum_four :
    ∑ n ∈ Finset.Icc 1 4, (ArithmeticFunction.moebius n : ℤ) = -1 := by
  have h1 : ArithmeticFunction.moebius 1 = 1 := ArithmeticFunction.moebius_apply_one
  have h2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_two
  have h3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime Nat.prime_three
  have h4 : ArithmeticFunction.moebius 4 = 0 := by
    refine ArithmeticFunction.moebius_eq_zero_of_not_squarefree ?_
    intro h
    have := h 2 (by norm_num)
    simp [Nat.isUnit_iff] at this
  have : Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) := by decide
  rw [this]
  norm_num [h1, h2, h3, h4]

/-- The determinant of the 4×4 Redheffer matrix equals the Mertens function
`M 4 = μ 1 + μ 2 + μ 3 + μ 4 = -1`. -/
theorem det_eq_mertens_4 :
    R4.det = ∑ n ∈ Finset.Icc 1 4, (ArithmeticFunction.moebius n : ℤ) := by
  rw [mertens_sum_four]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, R4, Matrix.submatrix]
  decide

end Riemann.Redheffer

