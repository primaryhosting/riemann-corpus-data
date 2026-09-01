import Mathlib
namespace Brockian.SophieGermain
/-- Sophie Germain's identity in action: a⁴ + 4b⁴ is composite for a,b > 1
    (it factors as (a²−2ab+2b²)(a²+2ab+2b²)). -/
theorem a4_add_4b4_not_prime (a b : ℕ) (ha : 1 < a) (hb : 1 < b) :
    ¬ (a ^ 4 + 4 * b ^ 4).Prime := by
  -- `d` is the smaller Sophie Germain factor `a² - 2ab + 2b²`, computed with
  -- truncated subtraction; `h2ab` guarantees the subtraction does not truncate.
  have h2ab : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by
    have := two_mul_le_add_sq a b; linarith
  have hb4 : 4 ≤ b ^ 2 := by nlinarith
  set d := a ^ 2 + 2 * b ^ 2 - 2 * (a * b) with hd
  have hS : a ^ 2 + 2 * b ^ 2 = d + 2 * (a * b) := by omega
  -- Sophie Germain's identity: (a² + 2b²)² - (2ab)² = a⁴ + 4b⁴.
  have key : a ^ 4 + 4 * b ^ 4 = d * (d + 4 * (a * b)) := by nlinarith [hS]
  have hd1 : 1 < d := by omega
  intro hp
  rcases hp.eq_one_or_self_of_dvd d ⟨_, key⟩ with h | h
  · omega
  · have h2 : d * 1 = d * (d + 4 * (a * b)) := by rw [mul_one, ← key, ← h]
    have h3 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < d) h2
    have hab1 : 1 ≤ a * b := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
end Brockian.SophieGermain

