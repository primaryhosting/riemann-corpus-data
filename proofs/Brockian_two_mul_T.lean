import Mathlib

/-!
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
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

namespace Brockian
namespace ConeLine

/-- The `n`-th triangular number. -/
def T (n : ℕ) : ℕ := n * (n + 1) / 2

lemma two_mul_T (n : ℕ) : 2 * T n = n * (n + 1) :=
  Nat.mul_div_cancel' (Nat.two_dvd_mul_add_one n)

lemma T_add_ten (n : ℕ) : T (n + 10) = T n + (10 * n + 55) := by
  have h : 2 * T (n + 10) = 2 * (T n + (10 * n + 55)) := by
    rw [two_mul_T (n + 10), mul_add 2 (T n) (10 * n + 55), two_mul_T n]
    ring
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

lemma T_mod_five_mem (n : ℕ) : T n % 5 = 0 ∨ T n % 5 = 1 ∨ T n % 5 = 3 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < 10
    · interval_cases n <;> simp [T]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
      have hm := ih m (by omega)
      rw [T_add_ten]
      omega

/-- Triangular numbers land only on rays `0`, `1`, `3` modulo `5`. -/
theorem triangular_mod5_mem (n : ℕ) :
    (T n : ZMod 5) ∈ ({0, 1, 3} : Set (ZMod 5)) := by
  have h : (T n : ZMod 5) = ((T n % 5 : ℕ) : ZMod 5) := by
    rw [ZMod.natCast_mod]
  rcases T_mod_five_mem n with h5 | h5 | h5 <;> rw [h, h5] <;> simp

end ConeLine
end Brockian

