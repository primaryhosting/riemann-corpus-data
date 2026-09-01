import Mathlib

/-!
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5`, `e x = ω ^ x.val`. -/
noncomputable def e (x : ZMod 5) : ℂ := ω ^ x.val

/-- Expanding a sum over `ZMod 5` into its five terms. -/
theorem sum_univ_zmod5 (f : ZMod 5 → ℂ) :
    ∑ x : ZMod 5, f x = f 0 + f 1 + f 2 + f 3 + f 4 := by
  show ∑ x : Fin 5, f x = _
  simp [Fin.sum_univ_five]

/-- The sum of all fifth powers of `ω` vanishes. -/
theorem sum_omega_pow : ∑ k ∈ Finset.range 5, ω ^ k = 0 := by
  have h := (Complex.isPrimitiveRoot_exp 5 (by norm_num)).geom_sum_eq_zero (by norm_num)
  simpa [ω] using h

/-- The additive character `e` sums to zero over `ZMod 5`. -/
theorem sum_e : ∑ x : ZMod 5, e x = 0 := by
  rw [sum_univ_zmod5]
  have h0 := sum_omega_pow
  simp [Finset.sum_range_succ] at h0
  simp only [e, show (0 : ZMod 5).val = 0 from rfl, show (1 : ZMod 5).val = 1 from rfl,
    show (2 : ZMod 5).val = 2 from rfl, show (3 : ZMod 5).val = 3 from rfl,
    show (4 : ZMod 5).val = 4 from rfl]
  linear_combination h0

/-- Additive-character orthogonality on `ZMod 5`:
`∑ x, e (a * x)` equals `5` when `a = 0` and `0` otherwise. -/
theorem sum_e_mul (a : ZMod 5) : ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  by_cases ha : a = 0
  · subst ha
    simp [e]
  · rw [if_neg ha,
      Fintype.sum_bijective (fun x => a * x) (Equiv.mulLeft₀ a ha).bijective _ e (fun _ => rfl)]
    exact sum_e

end Characters5
end Brockian

