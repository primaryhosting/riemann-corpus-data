/-
# Deutsch Jozsa
Category: Frontier Qi
Target: QI.deutsch_jozsa
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a module docstring `/-! ... -/`,
-- since Lean 4 requires `import` to be the first command in a file.)

import Mathlib

namespace QI

/-- The amplitude of the all-zeros outcome after the Deutsch–Jozsa circuit on an
`n`-qubit query register: after the Hadamard–oracle–Hadamard sandwich, the amplitude of
`|0…0⟩` is `2^(-n) * ∑_x (-1)^(f x)`. A single oracle query produces this amplitude. -/
noncomputable def djAmp (n : ℕ) (f : (Fin n → Bool) → Bool) : ℝ :=
  (∑ x : Fin n → Bool, (if f x then (-1 : ℝ) else 1)) / 2 ^ n

/-- `f` is constant. -/
def IsConstant {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop := ∀ x y, f x = f y

/-- `f` is balanced: it takes the value `true` on exactly as many inputs as `false`. -/
def IsBalanced {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  {x | f x = true}.toFinset.card = {x | f x = false}.toFinset.card

theorem sum_eq_card_diff {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (∑ x : Fin n → Bool, (if f x then (-1 : ℝ) else 1))
      = ({x | f x = false}.toFinset.card : ℝ) - ({x | f x = true}.toFinset.card : ℝ) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun x => f x = true)]
  have h1 : ∑ x ∈ Finset.univ.filter (fun x => f x = true), (if f x then (-1 : ℝ) else 1)
      = ∑ _x ∈ Finset.univ.filter (fun x => f x = true), (-1 : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp only [Finset.mem_filter] at hx
    simp [hx.2]
  have h2 : ∑ x ∈ Finset.univ.filter (fun x => ¬ (f x = true)), (if f x then (-1 : ℝ) else 1)
      = ∑ _x ∈ Finset.univ.filter (fun x => ¬ (f x = true)), (1 : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp only [Finset.mem_filter] at hx
    simp [hx.2]
  rw [h1, h2, Finset.sum_const, Finset.sum_const]
  have e1 : Finset.univ.filter (fun x : Fin n → Bool => f x = true)
      = {x | f x = true}.toFinset := by
    ext x; simp
  have e2 : Finset.univ.filter (fun x : Fin n → Bool => ¬ (f x = true))
      = {x | f x = false}.toFinset := by
    ext x; simp
  rw [e1, e2]
  push_cast
  ring

/-- **Deutsch–Jozsa.** With a single oracle query, the all-zeros measurement outcome
distinguishes constant from balanced functions: for a constant `f` the amplitude of the
all-zeros outcome has modulus `1` (so the outcome occurs with probability `1`), while for a
balanced `f` the amplitude is `0` (so the outcome never occurs). -/
theorem deutsch_jozsa (n : ℕ) (f : (Fin n → Bool) → Bool) :
    (IsConstant f → |djAmp n f| = 1) ∧ (IsBalanced f → djAmp n f = 0) := by
  classical
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  constructor
  · intro hc
    set x0 : Fin n → Bool := fun _ => false with hx0
    have hsum : (∑ x : Fin n → Bool, (if f x then (-1 : ℝ) else 1))
        = ∑ _x : Fin n → Bool, (if f x0 then (-1 : ℝ) else 1) := by
      refine Finset.sum_congr rfl ?_
      intro x _
      rw [hc x x0]
    have hcard : (Finset.univ : Finset (Fin n → Bool)).card = 2 ^ n := by
      simp [Finset.card_univ]
    rw [djAmp, hsum, Finset.sum_const, hcard]
    rcases hb : f x0 with _ | _
    · simp only [if_neg (by simp [hb])]
      rw [nsmul_eq_mul]
      push_cast
      rw [mul_one, div_self (ne_of_gt hpow)]
      norm_num
    · simp only [if_pos (by simp [hb])]
      rw [nsmul_eq_mul]
      push_cast
      rw [mul_neg, mul_one, neg_div, div_self (ne_of_gt hpow)]
      norm_num
  · intro hb
    rw [djAmp, sum_eq_card_diff, hb]
    simp

end QI

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

