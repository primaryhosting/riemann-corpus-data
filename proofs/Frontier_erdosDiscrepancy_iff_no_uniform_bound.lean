import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset

/-- A `±1` sequence, indexed by the positive integers. -/
def IsPlusMinusOne (f : ℕ → ℤ) : Prop := ∀ n, 1 ≤ n → f n = 1 ∨ f n = -1

/-- The discrepancy sum of `f` along the homogeneous arithmetic progression of common
difference `d`, truncated after `n` terms: `f d + f 2d + ⋯ + f nd`. -/
def apSum (f : ℕ → ℤ) (d n : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, f (i * d)

/-- **The Erdős discrepancy problem** (a theorem of Tao, 2015), as a formal statement:
every `±1` sequence has unbounded discrepancy along homogeneous arithmetic progressions,
i.e. for every bound `C` there are `d, n ≥ 1` with `|f d + f 2d + ⋯ + f nd| > C`. -/
def ErdosDiscrepancy : Prop :=
  ∀ f : ℕ → ℤ, IsPlusMinusOne f → ∀ C : ℤ, ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ C < |apSum f d n|

/-- Reduction: the Erdős discrepancy statement is equivalent to saying that no `±1`
sequence admits a uniform bound on its discrepancy over homogeneous APs. -/
theorem erdosDiscrepancy_iff_no_uniform_bound :
    ErdosDiscrepancy ↔
      ∀ f : ℕ → ℤ, IsPlusMinusOne f →
        ¬ ∃ C : ℤ, ∀ d n : ℕ, 0 < d → 0 < n → |apSum f d n| ≤ C := by
  constructor
  · rintro h f hf ⟨C, hC⟩
    obtain ⟨d, n, hd, hn, hlt⟩ := h f hf C
    exact absurd (hC d n hd hn) (not_le.2 hlt)
  · intro h f hf C
    by_contra hcon
    push_neg at hcon
    exact h f hf ⟨C, fun d n hd hn => hcon d n hd hn⟩

/-- Key finite step: a `±1` sequence whose discrepancy over homogeneous APs never exceeds
`1` does not exist.  Only the progressions with `d * n ≤ 12`, hence only the values
`f 1, …, f 12`, are involved. -/
theorem no_discrepancy_one_sequence (f : ℕ → ℤ) (hf : IsPlusMinusOne f)
    (H : ∀ d n : ℕ, 0 < d → 0 < n → d * n ≤ 12 → |apSum f d n| ≤ 1) : False := by
  simp only [apSum] at H
  have h1 := H 1 4 (by norm_num) (by norm_num) (by norm_num)
  have h2 := H 1 6 (by norm_num) (by norm_num) (by norm_num)
  have h3 := H 1 10 (by norm_num) (by norm_num) (by norm_num)
  have h4 := H 1 8 (by norm_num) (by norm_num) (by norm_num)
  have h5 := H 3 2 (by norm_num) (by norm_num) (by norm_num)
  have h6 := H 3 4 (by norm_num) (by norm_num) (by norm_num)
  have h7 := H 5 2 (by norm_num) (by norm_num) (by norm_num)
  have h8 := H 6 2 (by norm_num) (by norm_num) (by norm_num)
  rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from rfl] at h5 h7 h8
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) from rfl] at h1 h6
  rw [show Finset.Icc 1 6 = ({1, 2, 3, 4, 5, 6} : Finset ℕ) from rfl] at h2
  rw [show Finset.Icc 1 8 = ({1, 2, 3, 4, 5, 6, 7, 8} : Finset ℕ) from rfl] at h4
  rw [show Finset.Icc 1 10 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10} : Finset ℕ) from rfl] at h3
  simp only [abs_le] at h1 h2 h3 h4 h5 h6 h7 h8
  norm_num at h1 h2 h3 h4 h5 h6 h7 h8
  have a1 := hf 1 (by norm_num)
  have a2 := hf 2 (by norm_num)
  have a3 := hf 3 (by norm_num)
  have a4 := hf 4 (by norm_num)
  have a5 := hf 5 (by norm_num)
  have a6 := hf 6 (by norm_num)
  have a7 := hf 7 (by norm_num)
  have a8 := hf 8 (by norm_num)
  have a9 := hf 9 (by norm_num)
  have a10 := hf 10 (by norm_num)
  have a12 := hf 12 (by norm_num)
  omega

/-- A quantitative form of the base case: the progression witnessing discrepancy `≥ 2`
can be found among those with `d * n ≤ 12`, i.e. using only the values `f 1, …, f 12`. -/
theorem erdos_discrepancy_quantitative (f : ℕ → ℤ) (hf : IsPlusMinusOne f) :
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ d * n ≤ 12 ∧ 2 ≤ |apSum f d n| := by
  by_contra hcon
  push_neg at hcon
  refine no_discrepancy_one_sequence f hf (fun d n hd hn hdn => ?_)
  have := hcon d n hd hn hdn
  omega

/-- **Erdős discrepancy, base case.**  Every `±1` sequence has discrepancy at least `2`
along some homogeneous arithmetic progression: there are `d, n ≥ 1` with
`|f d + f 2d + ⋯ + f nd| ≥ 2`.  (This is the case `C = 1` of the full statement
`Frontier.ErdosDiscrepancy`.) -/
theorem erdos_discrepancy (f : ℕ → ℤ) (hf : IsPlusMinusOne f) :
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ 2 ≤ |apSum f d n| := by
  obtain ⟨d, n, hd, hn, -, h⟩ := erdos_discrepancy_quantitative f hf
  exact ⟨d, n, hd, hn, h⟩

/-- The base case, phrased as the instance `C = 1` of the general statement. -/
theorem erdos_discrepancy_case_one (f : ℕ → ℤ) (hf : IsPlusMinusOne f) :
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ (1 : ℤ) < |apSum f d n| := by
  obtain ⟨d, n, hd, hn, h⟩ := erdos_discrepancy f hf
  exact ⟨d, n, hd, hn, by omega⟩

/-- Dilation reduction: for every `k ≥ 1`, the dilated sequence `n ↦ f (k * n)` is again
a `±1` sequence, so the base case applies to it: the discrepancy bound `2` is attained on
homogeneous APs whose common difference is a multiple of `k`. -/
theorem erdos_discrepancy_dilate (f : ℕ → ℤ) (hf : IsPlusMinusOne f) (k : ℕ) (hk : 0 < k) :
    ∃ d n : ℕ, 0 < d ∧ 0 < n ∧ 2 ≤ |apSum f (k * d) n| := by
  obtain ⟨d, n, hd, hn, h⟩ := erdos_discrepancy (fun m => f (k * m))
    (fun m hm => hf (k * m) (Nat.one_le_iff_ne_zero.2 (by positivity)))
  refine ⟨d, n, hd, hn, ?_⟩
  have : apSum (fun m => f (k * m)) d n = apSum f (k * d) n := by
    simp only [apSum]
    exact Finset.sum_congr rfl fun i _ => by ring_nf
  rwa [this] at h

end Frontier

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

