import Mathlib

/-!
# Square Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.square_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ConeLine

/-- Perfect squares land only on rays `0`, `1`, `4`: for every `n : ZMod 5`,
`n ^ 2` is `0`, `1` or `4` (rays `2` and `3` are square-free). -/
theorem square_mod5_mem (n : ZMod 5) : n ^ 2 = 0 ∨ n ^ 2 = 1 ∨ n ^ 2 = 4 := by
  revert n
  decide +kernel

/-- Integer form: for every `n : ℤ`, the class of `n ^ 2` in `ZMod 5` is `0`, `1` or `4`. -/
theorem square_mod5_mem_int (n : ℤ) :
    ((n ^ 2 : ℤ) : ZMod 5) = 0 ∨ ((n ^ 2 : ℤ) : ZMod 5) = 1 ∨ ((n ^ 2 : ℤ) : ZMod 5) = 4 := by
  rw [Int.cast_pow]
  exact square_mod5_mem (n : ZMod 5)

/-- `Finset` membership form of `square_mod5_mem`. -/
theorem square_mod5_mem_finset (n : ZMod 5) : n ^ 2 ∈ ({0, 1, 4} : Finset (ZMod 5)) := by
  simpa only [Finset.mem_insert, Finset.mem_singleton] using square_mod5_mem n

/-- Integer/`Int.emod` form: `n ^ 2 % 5 ∈ {0, 1, 4}` for every integer `n`. -/
theorem square_mod5_emod_mem (n : ℤ) : n ^ 2 % 5 = 0 ∨ n ^ 2 % 5 = 1 ∨ n ^ 2 % 5 = 4 := by
  have h : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  have hsq : n ^ 2 % 5 = (n % 5) ^ 2 % 5 := by
    rw [pow_two, pow_two, Int.mul_emod]
  rcases h with h | h | h | h | h <;> rw [hsq, h] <;> norm_num

end Brockian.ConeLine

