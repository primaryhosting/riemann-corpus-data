/-!
# Integrality Three Halves
Category: Riemann Program
Target: Riemann.Method.integrality_three_halves
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Riemann.Method

/-- **Integrality (three halves).** For every natural number `m`, `3 * m ≤ m ^ 2 + 2`.

Over the integers this is exactly `(m - 1) * (m - 2) ≥ 0`, the integrality step one level
above `m ^ 2 ≥ 2 * m - 1`. -/
theorem integrality_three_halves (m : Nat) : 3 * m ≤ m ^ 2 + 2 := by
  induction m with
  | zero => decide
  | succ k ih =>
    have hk : k ≤ k * k := by
      cases k with
      | zero => decide
      | succ n => exact Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
    have hsucc : (k + 1) ^ 2 = (k + 1) * (k + 1) := Nat.pow_two (k + 1)
    have hsq : k ^ 2 = k * k := Nat.pow_two k
    rw [hsucc]
    rw [hsq] at ih
    have hexp : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by
      simp [Nat.succ_mul, Nat.mul_succ]
      omega
    omega

end Riemann.Method

