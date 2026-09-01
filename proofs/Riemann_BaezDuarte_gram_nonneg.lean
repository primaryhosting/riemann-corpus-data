import Mathlib

/-!
# Gram Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.BaezDuarte.gram_nonneg
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
namespace BaezDuarte

/-- **Gram nonnegativity (clean self-contained case).**
For all reals `a b`, the quadratic form `a^2 - 2ab + b^2` is nonnegative,
since it is the perfect square `(a - b)^2`.  This is the Gram/distance
nonnegativity underlying the Nyman–Beurling / Baez-Duarte distance, which is a
sum of such squares.  (Closed by `sq_nonneg` after `nlinarith`/`ring_nf`.) -/
theorem gram_nonneg (a b : ℝ) : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
  have h : a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
  rw [h]
  exact sq_nonneg _

/-- **Gram nonnegativity, general finite form.**
In any real inner product space `V`, for any finite family of vectors
`v : Fin n → V` and coefficients `c : Fin n → ℝ`, the Gram quadratic form
`∑ i, ∑ j, c i * c j * ⟪v i, v j⟫` is nonnegative, being the squared norm of
`∑ i, c i • v i`. -/
theorem gram_sum_nonneg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (n : ℕ) (v : Fin n → V) (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * (inner ℝ (v i) (v j) : ℝ) := by
  have key : ∑ i, ∑ j, c i * c j * (inner ℝ (v i) (v j) : ℝ)
      = ‖∑ i, c i • v i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp only [inner_sum, real_inner_smul_left, real_inner_smul_right]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [key]
  exact sq_nonneg _

end BaezDuarte
end Riemann

