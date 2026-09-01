/-
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header block is repeated above as a plain comment because Lean requires
`import` to be the first command of the file, before any module docstring.)
-/

namespace CS

/-- **Master theorem, case 1.**

The divide-and-conquer recurrence `T(n) = a * T(n / b) + f(n)` is analysed, as usual, along
the powers `n = b ^ k` of the branching factor: `T k` below stands for `T (b ^ k)`, so that the
recurrence reads `T (k+1) = a * T k + f (k+1)`.

If the driving function satisfies `f(n) = O(n ^ (log_b a - ε))` for some `ε > 0` (here in the
explicit form `f (b^k) ≤ C * (b^k) ^ (log_b a - ε)`), and `T (b^0) > 0`, then
`T(n) = Θ(n ^ (log_b a))`: there are positive constants `c₁, c₂` with
`c₁ * n ^ (log_b a) ≤ T(n) ≤ c₂ * n ^ (log_b a)` for all `n = b ^ k`. -/
theorem master_theorem_case1
    (a b eps C T0 : ℝ) (f T : ℕ → ℝ)
    (ha : 0 < a) (hb : 1 < b) (heps : 0 < eps)
    (hT0 : T 0 = T0) (hT0pos : 0 < T0)
    (hrec : ∀ k : ℕ, T (k + 1) = a * T k + f (k + 1))
    (hfnonneg : ∀ k : ℕ, 0 ≤ f k)
    (hfO : ∀ k : ℕ, f k ≤ C * ((b : ℝ) ^ k) ^ (Real.logb b a - eps)) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ k : ℕ, c₁ * ((b : ℝ) ^ k) ^ (Real.logb b a) ≤ T k ∧
               T k ≤ c₂ * ((b : ℝ) ^ k) ^ (Real.logb b a) := by
  have hbpos : (0 : ℝ) < b := lt_trans zero_lt_one hb
  set p : ℝ := Real.logb b a with hp
  -- `b ^ p = a`
  have hbp : b ^ p = a := Real.rpow_logb hbpos hb.ne' ha
  -- moving a natural power inside an `rpow`
  have hswap : ∀ (x : ℝ) (k : ℕ), ((b : ℝ) ^ k) ^ x = (b ^ x) ^ k := by
    intro x k
    rw [← Real.rpow_natCast b k, ← Real.rpow_mul hbpos.le, mul_comm,
      Real.rpow_mul hbpos.le, Real.rpow_natCast]
  have hpow : ∀ k : ℕ, ((b : ℝ) ^ k) ^ p = a ^ k := by
    intro k; rw [hswap, hbp]
  -- the shrink factor `r = b ^ (-eps) ∈ (0,1)`
  obtain ⟨r, hr0, hr1, hpow2⟩ :
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ k : ℕ, ((b : ℝ) ^ k) ^ (p - eps) = (a * r) ^ k := by
    have hs1 : 1 < b ^ eps := Real.one_lt_rpow hb heps
    have hspos : (0 : ℝ) < b ^ eps := lt_trans zero_lt_one hs1
    refine ⟨(b ^ eps)⁻¹, inv_pos.2 hspos, inv_lt_one_of_one_lt₀ hs1, fun k => ?_⟩
    rw [hswap, Real.rpow_sub hbpos, hbp, div_eq_mul_inv]
  -- the implied constant is nonnegative
  have hC : 0 ≤ C := by
    have h0 := hfO 0
    have h1 := hfnonneg 0
    simp only [pow_zero, Real.one_rpow, mul_one] at h0
    linarith
  -- the total extra work, distributed as a decreasing budget
  obtain ⟨B, hBnonneg, hBeq⟩ : ∃ B : ℝ, 0 ≤ B ∧ B * (1 - r) = C * r := by
    have h1r : (1 : ℝ) - r ≠ 0 := by linarith
    refine ⟨C * r / (1 - r), div_nonneg (mul_nonneg hC hr0.le) (by linarith), ?_⟩
    field_simp
  set A : ℝ := T0 + B with hAdef
  have hApos : 0 < A := by positivity
  -- upper bound with a decreasing "budget"
  have hupper : ∀ k : ℕ, T k ≤ (A - B * r ^ k) * a ^ k := by
    intro k
    induction k with
    | zero => simp [hT0, hAdef]
    | succ k ih =>
      have hfk : f (k + 1) ≤ C * (a * r) ^ (k + 1) := by
        have := hfO (k + 1)
        rwa [hpow2] at this
      have h1 : a * T k ≤ a * ((A - B * r ^ k) * a ^ k) :=
        mul_le_mul_of_nonneg_left ih ha.le
      have hkey : a * ((A - B * r ^ k) * a ^ k) + C * (a * r) ^ (k + 1)
          = (A - B * r ^ (k + 1)) * a ^ (k + 1) := by
        linear_combination (-(a ^ (k + 1) * r ^ k)) * hBeq
      calc T (k + 1) = a * T k + f (k + 1) := hrec k
        _ ≤ a * ((A - B * r ^ k) * a ^ k) + C * (a * r) ^ (k + 1) := by linarith
        _ = (A - B * r ^ (k + 1)) * a ^ (k + 1) := hkey
  -- lower bound
  have hlower : ∀ k : ℕ, T0 * a ^ k ≤ T k := by
    intro k
    induction k with
    | zero => simp [hT0]
    | succ k ih =>
      have h1 : a * (T0 * a ^ k) ≤ a * T k := mul_le_mul_of_nonneg_left ih ha.le
      have h2 : 0 ≤ f (k + 1) := hfnonneg (k + 1)
      have h3 : T0 * a ^ (k + 1) = a * (T0 * a ^ k) := by ring
      rw [hrec k, h3]
      linarith
  refine ⟨T0, A, hT0pos, hApos, fun k => ⟨?_, ?_⟩⟩
  · rw [hpow k]; exact hlower k
  · rw [hpow k]
    have h1 : 0 ≤ B * r ^ k := mul_nonneg hBnonneg (pow_pos hr0 k).le
    have h2 : (0 : ℝ) < a ^ k := pow_pos ha k
    nlinarith [hupper k]

end CS

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

