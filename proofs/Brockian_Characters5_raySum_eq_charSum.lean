/-
# Ray Sum Eq Char Sum
Category: Characters
Target: Brockian.Characters5.raySum_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5` with values in `ℂ`. -/
noncomputable def e (x : ZMod 5) : ℂ := ω ^ x.val

/-- The number of elements of a finite set `S` of naturals lying on the ray `r` mod `5`. -/
def raySum (S : Finset ℕ) (r : ZMod 5) : ℕ := (S.filter fun n : ℕ => ((n : ZMod 5) = r)).card

lemma omega_isPrimitiveRoot : IsPrimitiveRoot ω 5 := by
  simpa [ω] using Complex.isPrimitiveRoot_exp 5 (by norm_num)

lemma omega_geom_sum : (1 : ℂ) + ω + ω ^ 2 + ω ^ 3 + ω ^ 4 = 0 := by
  have h := omega_isPrimitiveRoot.geom_sum_eq_zero (by norm_num)
  simpa [Finset.sum_range_succ] using h

/-- The character values of `e` over all of `ZMod 5` sum to zero. -/
lemma sum_e_univ : ∑ b : ZMod 5, e b = 0 := by
  have h : ∑ b : ZMod 5, e b = ∑ b : Fin 5, ω ^ (b : ℕ) := rfl
  have h2 := omega_geom_sum
  rw [h, Fin.sum_univ_five]
  norm_num
  linear_combination h2

/-- Orthogonality of the additive characters of `ZMod 5`. -/
lemma charSum_eq (x : ZMod 5) :
    ∑ a : ZMod 5, e (a * x) = if x = 0 then (5 : ℂ) else 0 := by
  by_cases hx : x = 0
  · subst hx
    simp [e]
  · rw [if_neg hx]
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have h := Equiv.sum_comp (Equiv.mulRight₀ x hx) e
    simpa [Equiv.mulRight₀] using h.trans sum_e_univ

/-- The indicator of the ray through `r`, expressed as a character sum. -/
lemma rayIndicator_eq_charSum (n r : ZMod 5) :
    (if n = r then (1 : ℂ) else 0) = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * (n - r)) := by
  rw [charSum_eq]
  by_cases h : n = r
  · simp [h]
  · simp [h, sub_ne_zero_of_ne h]

/-- Ray-count identity: the number of elements of `S` on the ray `r` mod `5` equals
`(1/5) ∑_{a : ZMod 5} ∑_{n ∈ S} e (a * (n - r))`. -/
theorem raySum_eq_charSum (S : Finset ℕ) (r : ZMod 5) :
    ((raySum S r : ℕ) : ℂ) = (1 / 5 : ℂ) * ∑ a : ZMod 5, ∑ n ∈ S, e (a * ((n : ZMod 5) - r)) := by
  rw [raySum, Finset.card_filter]
  push_cast
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => rayIndicator_eq_charSum (n : ZMod 5) r

end Brockian.Characters5

