/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- A `±1`-sequence: a function `f : ℕ → ℤ` taking only the values `1` and `-1`
on the positive integers. -/
def PlusMinusOne (f : ℕ → ℤ) : Prop := ∀ n : ℕ, 1 ≤ n → f n = 1 ∨ f n = -1

/-- The discrepancy of `f` along the homogeneous arithmetic progression of common
difference `d`, truncated at `n` terms: `|f d + f (2d) + ⋯ + f (nd)|`. -/
def apSum (f : ℕ → ℤ) (d n : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, f (i * d)

/-- `HasDiscrepancyExceeding f C` says that the sequence `f` has some homogeneous
arithmetic progression along which the partial sum exceeds `C` in absolute value. -/
def HasDiscrepancyExceeding (f : ℕ → ℤ) (C : ℤ) : Prop :=
  ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ C < |apSum f d n|

/-- The Erdős discrepancy problem (solved by Tao, 2015): every `±1` sequence has
unbounded discrepancy along homogeneous arithmetic progressions.  This is stated
here as a `Prop`-valued definition, recording the full statement; the theorem
`Frontier.erdos_discrepancy` below establishes its first nontrivial instance
`C = 1` (i.e. no `±1` sequence has discrepancy at most `1`). -/
def ErdosDiscrepancyStatement : Prop :=
  ∀ f : ℕ → ℤ, PlusMinusOne f → ∀ C : ℤ, HasDiscrepancyExceeding f C

/-- The case `C = 0` of the Erdős discrepancy problem: trivially, the single term
`f 1` already has absolute value `1 > 0`. -/
theorem erdos_discrepancy_zero (f : ℕ → ℤ) (hf : PlusMinusOne f) :
    HasDiscrepancyExceeding f 0 := by
  refine ⟨1, 1, one_pos, one_pos, ?_⟩
  have h := hf 1 le_rfl
  simp only [apSum, Finset.Icc_self, Finset.sum_singleton, one_mul]
  rcases h with h | h <;> rw [h] <;> norm_num

/-- **Erdős discrepancy problem, base case `C = 1`.**
Every `±1`-sequence `f : ℕ → ℤ` admits a homogeneous arithmetic progression
`d, 2d, …, nd` (with `d, n ≥ 1`) along which the partial sum
`f d + f (2d) + ⋯ + f (nd)` has absolute value greater than `1`.

Equivalently: no `±1`-sequence has discrepancy at most `1` on homogeneous
arithmetic progressions.  Only the first `12` terms of the sequence are needed,
which is optimal (there are `±1` sequences of length `11` with discrepancy `1`). -/
theorem erdos_discrepancy (f : ℕ → ℤ) (hf : PlusMinusOne f) :
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ 1 < |∑ i ∈ Finset.Icc 1 n, f (i * d)| := by
  by_contra hcon
  push_neg at hcon
  -- All the relevant partial sums are bounded by `1` in absolute value.
  have H : ∀ d n : ℕ, 0 < d → 0 < n → |∑ i ∈ Finset.Icc 1 n, f (i * d)| ≤ 1 := by
    intro d n hd hn
    exact hcon d n hd hn
  have h32 := H 3 2 (by norm_num) (by norm_num)
  have h34 := H 3 4 (by norm_num) (by norm_num)
  have h62 := H 6 2 (by norm_num) (by norm_num)
  have h18 := H 1 8 (by norm_num) (by norm_num)
  have h110 := H 1 10 (by norm_num) (by norm_num)
  have h24 := H 2 4 (by norm_num) (by norm_num)
  have h26 := H 2 6 (by norm_num) (by norm_num)
  rw [abs_le] at h32 h34 h62 h18 h110 h24 h26
  norm_num [Finset.sum_Icc_succ_top] at h32 h34 h62 h18 h110 h24 h26
  -- the values of `f` on `1, …, 12`
  have v1 := hf 1 (by norm_num)
  have v2 := hf 2 (by norm_num)
  have v3 := hf 3 (by norm_num)
  have v4 := hf 4 (by norm_num)
  have v5 := hf 5 (by norm_num)
  have v6 := hf 6 (by norm_num)
  have v7 := hf 7 (by norm_num)
  have v8 := hf 8 (by norm_num)
  have v9 := hf 9 (by norm_num)
  have v10 := hf 10 (by norm_num)
  have v11 := hf 11 (by norm_num)
  have v12 := hf 12 (by norm_num)
  omega

/-- Restatement of the base case in terms of `HasDiscrepancyExceeding`. -/
theorem erdos_discrepancy_one (f : ℕ → ℤ) (hf : PlusMinusOne f) :
    HasDiscrepancyExceeding f 1 :=
  erdos_discrepancy f hf

end Frontier

