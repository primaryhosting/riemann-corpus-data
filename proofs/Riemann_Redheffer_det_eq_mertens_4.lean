/-
# Det Eq Mertens 4
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.Redheffer.det_eq_mertens_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The `4 × 4` Redheffer matrix: `R i j = 1` if `j = 0` or `(i+1) ∣ (j+1)`
(using the `0`-indexed entries `i j : Fin 4`), and `0` otherwise. -/
def R : Matrix (Fin 4) (Fin 4) ℤ :=
  Matrix.of fun i j => if j = 0 ∨ (i.val + 1) ∣ (j.val + 1) then 1 else 0

/-- The determinant of the `4 × 4` Redheffer matrix equals the Mertens function
`M 4 = μ 1 + μ 2 + μ 3 + μ 4 = 1 - 1 - 1 + 0 = -1`. -/
theorem det_eq_mertens_4 :
    R.det = -1 ∧
      (-1 : ℤ) = ∑ n ∈ Finset.Icc 1 4, (ArithmeticFunction.moebius n : ℤ) := by
  constructor
  · rw [Matrix.det_fin_four]
    norm_num [R]
  · decide

end Redheffer
end Riemann

