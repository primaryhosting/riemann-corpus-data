import Mathlib

/-!
# Ray Indicator Eq Char Sum
Category: Characters
Target: Brockian.Characters5.rayIndicator_eq_charSum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The standard additive character of `ZMod 5` into `ℂ`. -/
noncomputable def e (a : ZMod 5) : ℂ := omega ^ a.val

lemma isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 := by
  simpa [omega] using Complex.isPrimitiveRoot_exp 5 (by norm_num)

lemma omega_pow_five : omega ^ 5 = 1 := isPrimitiveRoot_omega.pow_eq_one

lemma sum_e : ∑ c : ZMod 5, e c = 0 := by
  have h : ∑ i ∈ Finset.range 5, omega ^ i = 0 :=
    isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)
  calc ∑ c : ZMod 5, e c = ∑ i ∈ Finset.range 5, omega ^ i := by
        simp only [e]
        exact Finset.sum_nbij' (fun c => c.val) (fun i => (i : ZMod 5))
          (by intro c _; simpa using c.val_lt)
          (by intro i _; exact Finset.mem_univ _)
          (by intro c _; simp [ZMod.natCast_val, ZMod.cast_id])
          (by intro i hi; simp only [Finset.mem_range] at hi
              exact ZMod.val_natCast_of_lt hi)
          (by intro c _; rfl)
    _ = 0 := h

/-- Orthogonality of the character `e`. -/
lemma sum_e_mul (b : ZMod 5) : ∑ a : ZMod 5, e (b * a) = if b = 0 then 5 else 0 := by
  by_cases hb : b = 0
  · subst hb
    simp [e]
  · rw [if_neg hb]
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have : ∑ a : ZMod 5, e (b * a) = ∑ c : ZMod 5, e c :=
      Fintype.sum_equiv (Equiv.mulLeft₀ b hb) _ _ (fun a => rfl)
    rw [this, sum_e]

/-- Indicator of the ray `n ≡ r (mod 5)`. -/
noncomputable def rayIndicator (r : ZMod 5) (n : ℕ) : ℂ := if (n : ZMod 5) = r then 1 else 0

theorem rayIndicator_eq_charSum (r : ZMod 5) (n : ℕ) :
    rayIndicator r n = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r)) := by
  set b : ZMod 5 := (n : ZMod 5) - r with hbdef
  have hsum : ∑ a : ZMod 5, e (a * b) = ∑ a : ZMod 5, e (b * a) := by
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [mul_comm]
  rw [hsum, sum_e_mul, rayIndicator]
  have hiff : b = 0 ↔ (n : ZMod 5) = r := by
    rw [hbdef, sub_eq_zero]
  by_cases h : (n : ZMod 5) = r
  · rw [if_pos h, if_pos (hiff.mpr h)]
    norm_num
  · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]
    norm_num

end Characters5
end Brockian

