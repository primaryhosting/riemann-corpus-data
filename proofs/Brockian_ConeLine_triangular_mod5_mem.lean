/-
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian
namespace ConeLine

/-- The `n`-th triangular number, `T n = n(n+1)/2` (natural-number division,
which is exact since `n(n+1)` is even). -/
def T (n : ℕ) : ℕ := n * (n + 1) / 2

/-- Shifting the index by `10` does not change a triangular number modulo `5`:
`T (n + 10) = T n + 10 * n + 55`. -/
lemma T_add_ten_mod_five (n : ℕ) : T (n + 10) % 5 = T n % 5 := by
  have hx : (n + 10) * (n + 10 + 1) = n * (n + 1) + 20 * n + 110 := by ring
  have h2 : 2 ∣ n * (n + 1) := (Nat.even_mul_succ_self n).two_dvd
  unfold T
  rw [hx]
  omega

/-- Modulo `5`, a triangular number is `0`, `1` or `3`. -/
lemma T_mod_five (n : ℕ) : T n % 5 = 0 ∨ T n % 5 = 1 ∨ T n % 5 = 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n 10 with h | h
    · interval_cases n <;> decide
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
      rw [T_add_ten_mod_five]
      exact ih m (by omega)

/-- **Triangular numbers land only on rays `0`, `1`, `3` modulo `5`.**
For every `n`, the triangular number `T n = n(n+1)/2`, viewed in `ZMod 5`,
lies in `{0, 1, 3}`; rays `2` and `4` carry no triangular number. -/
theorem triangular_mod5_mem (n : ℕ) : ((T n : ℕ) : ZMod 5) ∈ ({0, 1, 3} : Set (ZMod 5)) := by
  have h : ((T n : ℕ) : ZMod 5) = ((T n % 5 : ℕ) : ZMod 5) := (ZMod.natCast_mod _ _).symm
  rcases T_mod_five n with h5 | h5 | h5 <;> rw [h, h5] <;> simp

end ConeLine
end Brockian

