import Mathlib
/-!
# Euler Product Term Ne Zero
Category: Riemann Program
Target: Riemann.zeta.euler_product_term_ne_zero
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
namespace zeta

/-- For `p` a prime and `s` with `1 < s.re`, the Euler factor `1 - p ^ (-s)` is nonzero. -/
theorem euler_product_term_ne_zero {s : ℂ} (hs : 1 < s.re) {p : ℕ} (hp : p.Prime) :
    (1 - (p : ℂ) ^ (-s)) ≠ 0 := by
  have hp2 : (2 : ℕ) ≤ p := hp.two_le
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hp2
  have hppos : (0 : ℝ) < (p : ℝ) := lt_trans one_pos hp1
  have hnorm : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    have := Complex.norm_cpow_eq_rpow_re_of_pos (x := (p : ℝ)) hppos (-s)
    simpa using this
  have hlt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [hnorm]
    refine Real.rpow_lt_one_of_one_lt_of_neg hp1 ?_
    simp only [Left.neg_neg_iff]
    linarith
  intro h
  have hone : (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  rw [hone] at hlt
  simp at hlt

end zeta
end Riemann

