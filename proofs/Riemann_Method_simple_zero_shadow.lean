/-!
# Simple Zero Shadow
Category: Riemann Program
Target: Riemann.Method.simple_zero_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Riemann
namespace Method

/-- Expansion of `(k + 1) ^ 2`, stated with `Nat` multiplication so that `omega`
can treat `k * k` as an atom. -/
private theorem sq_succ_expand (k : Nat) : (k + 1) ^ 2 = k * k + 2 * k + 1 := by
  simp [Nat.pow_succ, Nat.add_mul, Nat.mul_add]
  omega

/-- `k ≤ k * k` for every natural number `k`. -/
private theorem self_le_mul_self (k : Nat) : k ≤ k * k := by
  rcases k with _ | j
  · exact Nat.le_refl 0
  · exact Nat.le_mul_of_pos_left _ (Nat.succ_pos j)

/-- **Simple zero shadow.**  For every natural number `m` with `1 ≤ m` we have
`2 * m ≤ m ^ 2 + 1`, and equality holds precisely when `m = 1`.
This is the integrality step `(m - 1) ^ 2 ≥ 0` that separates simple zeros in
Montgomery's two-thirds argument. -/
theorem simple_zero_shadow :
    ∀ m : Nat, 1 ≤ m → 2 * m ≤ m ^ 2 + 1 ∧ (2 * m = m ^ 2 + 1 ↔ m = 1) := by
  intro m hm
  obtain ⟨k, rfl⟩ : ∃ k : Nat, m = k + 1 := ⟨m - 1, by omega⟩
  have hsq := sq_succ_expand k
  have hkk := self_le_mul_self k
  refine ⟨by omega, ?_, ?_⟩
  · intro h
    omega
  · intro h
    have hk0 : k = 0 := by omega
    subst hk0
    decide

end Method
end Riemann

