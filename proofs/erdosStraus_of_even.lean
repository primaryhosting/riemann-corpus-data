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

import Mathlib

/-- `4 / n` is a sum of three unit fractions with positive denominators. -/
def ErdosStrausSolvable (n : ℕ) : Prop :=
  ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    (4 : ℚ) / (n : ℚ) = 1 / (a : ℚ) + 1 / (b : ℚ) + 1 / (c : ℚ)

/-- The Erdős–Straus conjecture (**OPEN**), recorded as an unproven
`def`: every `n ≥ 2` admits such a representation. -/
def ErdosStrausConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ErdosStrausSolvable n

theorem erdosStraus_of_even {n : ℕ} (hn : 2 ≤ n) (he : Even n) :
    ErdosStrausSolvable n := by
  obtain ⟨m, hm⟩ := he
  have hm1 : 1 ≤ m := by omega
  subst hm
  refine ⟨m, m + 1, m * (m + 1), by omega, by omega, by positivity, ?_⟩
  have hmQ : (0 : ℚ) < (m : ℚ) := by exact_mod_cast hm1
  have h1 : ((m + m : ℕ) : ℚ) = 2 * (m : ℚ) := by push_cast; ring
  have h2 : ((m + 1 : ℕ) : ℚ) = (m : ℚ) + 1 := by push_cast; ring
  have h3 : ((m * (m + 1) : ℕ) : ℚ) = (m : ℚ) * ((m : ℚ) + 1) := by push_cast; ring
  rw [h1, h2, h3]
  have hm1' : (m : ℚ) + 1 ≠ 0 := by positivity
  field_simp
  ring

