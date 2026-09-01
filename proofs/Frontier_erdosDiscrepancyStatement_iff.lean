/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Frontier

/-- `f` is a `±1`-valued sequence (only the positive indices matter). -/
def IsPMOne (f : ℕ → ℤ) : Prop := ∀ n, 1 ≤ n → f n = 1 ∨ f n = -1

/-- The discrepancy sum of `f` along the homogeneous arithmetic progression with
common difference `d` and length `n`, i.e. `f d + f (2d) + ⋯ + f (n d)`. -/
def apSum (f : ℕ → ℤ) (n d : ℕ) : ℤ := ∑ i ∈ Finset.Icc 1 n, f (i * d)

/-- The Erdős discrepancy statement (Tao's theorem): every `±1` sequence has
unbounded discrepancy along homogeneous arithmetic progressions. -/
def ErdosDiscrepancyStatement : Prop :=
  ∀ f : ℕ → ℤ, IsPMOne f → ∀ C : ℤ, ∃ n d : ℕ, 0 < n ∧ 0 < d ∧ C < |apSum f n d|

/-- Reduction: the Erdős discrepancy statement is equivalent to saying that no
`±1` sequence has discrepancy bounded by some constant `C`. -/
theorem erdosDiscrepancyStatement_iff :
    ErdosDiscrepancyStatement ↔
      ∀ f : ℕ → ℤ, IsPMOne f → ∀ C : ℤ,
        ¬ (∀ n d : ℕ, 0 < n → 0 < d → |apSum f n d| ≤ C) := by
  constructor
  · intro h f hf C hC
    obtain ⟨n, d, hn, hd, hlt⟩ := h f hf C
    exact absurd (hC n d hn hd) (not_le.2 hlt)
  · intro h f hf C
    by_contra hcon
    push_neg at hcon
    exact h f hf C fun n d hn hd => hcon n d hn hd

section Helpers

variable {a b : ℤ}

/-- If `a, b ∈ {±1}` and `|a + b| < 2`, then `b = -a`. -/
theorem pm_add_eq_neg (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
    (h : |a + b| < 2) : b = -a := by
  rw [abs_lt] at h
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> omega

end Helpers

/-- **Base case of the Erdős discrepancy problem** (`C = 1`): no `±1` sequence
has discrepancy at most `1` along homogeneous arithmetic progressions.  Every
`±1` sequence admits a homogeneous arithmetic progression on which the sum has
absolute value at least `2`. -/
theorem erdos_discrepancy_base (f : ℕ → ℤ) (hf : IsPMOne f) :
    ∃ n d : ℕ, 0 < n ∧ 0 < d ∧ 2 ≤ |apSum f n d| := by
  by_contra hcon
  push_neg at hcon
  -- the ±1 values
  have p1 := hf 1 (by norm_num)
  have p2 := hf 2 (by norm_num)
  have p3 := hf 3 (by norm_num)
  have p4 := hf 4 (by norm_num)
  have p5 := hf 5 (by norm_num)
  have p6 := hf 6 (by norm_num)
  have p7 := hf 7 (by norm_num)
  have p8 := hf 8 (by norm_num)
  have p9 := hf 9 (by norm_num)
  have p10 := hf 10 (by norm_num)
  have p12 := hf 12 (by norm_num)
  -- the discrepancy bounds we shall use
  have e21 : |f 1 + f 2| < 2 := by
    have h := hcon 2 1 (by norm_num) (by norm_num)
    simpa [apSum, Finset.sum_Icc_succ_top] using h
  have e22 : |f 2 + f 4| < 2 := by
    have h := hcon 2 2 (by norm_num) (by norm_num)
    simpa [apSum, Finset.sum_Icc_succ_top] using h
  have e23 : |f 3 + f 6| < 2 := by
    have h := hcon 2 3 (by norm_num) (by norm_num)
    simpa [apSum, Finset.sum_Icc_succ_top] using h
  have e24 : |f 4 + f 8| < 2 := by
    have h := hcon 2 4 (by norm_num) (by norm_num)
    simpa [apSum, Finset.sum_Icc_succ_top] using h
  have e25 : |f 5 + f 10| < 2 := by
    have h := hcon 2 5 (by norm_num) (by norm_num)
    simpa [apSum, Finset.sum_Icc_succ_top] using h
  have e26 : |f 6 + f 12| < 2 := by
    have h := hcon 2 6 (by norm_num) (by norm_num)
    simpa [apSum, Finset.sum_Icc_succ_top] using h
  have e41 : |f 1 + f 2 + f 3 + f 4| < 2 := by
    have h := hcon 4 1 (by norm_num) (by norm_num)
    simpa [apSum, Finset.sum_Icc_succ_top] using h
  have e43 : |f 3 + f 6 + f 9 + f 12| < 2 := by
    have h := hcon 4 3 (by norm_num) (by norm_num)
    simpa [apSum, Finset.sum_Icc_succ_top] using h
  have e61 : |f 1 + f 2 + f 3 + f 4 + f 5 + f 6| < 2 := by
    have h := hcon 6 1 (by norm_num) (by norm_num)
    simpa [apSum, Finset.sum_Icc_succ_top] using h
  have e81 : |f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8| < 2 := by
    have h := hcon 8 1 (by norm_num) (by norm_num)
    simpa [apSum, Finset.sum_Icc_succ_top] using h
  have e101 : |f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10| < 2 := by
    have h := hcon 10 1 (by norm_num) (by norm_num)
    simpa [apSum, Finset.sum_Icc_succ_top] using h
  -- doubling relations
  have h2 : f 2 = -f 1 := pm_add_eq_neg p1 p2 e21
  have h4 : f 4 = -f 2 := pm_add_eq_neg p2 p4 e22
  have h6 : f 6 = -f 3 := pm_add_eq_neg p3 p6 e23
  have h8 : f 8 = -f 4 := pm_add_eq_neg p4 p8 e24
  have h10 : f 10 = -f 5 := pm_add_eq_neg p5 p10 e25
  have h12 : f 12 = -f 6 := pm_add_eq_neg p6 p12 e26
  -- tripling: f 3 = - f 1 and f 9 = - f 3
  have h3 : f 3 = -f 1 := by
    refine pm_add_eq_neg p1 p3 ?_
    have : f 1 + f 3 = f 1 + f 2 + f 3 + f 4 := by omega
    rw [this]; exact e41
  have h9 : f 9 = -f 3 := by
    refine pm_add_eq_neg p3 p9 ?_
    have : f 3 + f 9 = f 3 + f 6 + f 9 + f 12 := by omega
    rw [this]; exact e43
  -- quintupling at 1: f 5 = - f 1
  have h5 : f 5 = -f 1 := by
    refine pm_add_eq_neg p1 p5 ?_
    have : f 1 + f 5 = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by omega
    rw [this]; exact e61
  -- f 7 = f 1
  have h7 : f 7 = -(-f 1) := by
    refine pm_add_eq_neg (by omega) p7 ?_
    have : -f 1 + f 7 = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 := by omega
    rw [this]; exact e81
  -- final contradiction: the sum of the first ten terms is `2 * f 1`
  rw [abs_lt] at e101
  rcases p1 with hp | hp <;> omega

/-- **Erdős discrepancy problem** (Tao's theorem), formalized, together with a
Lean-checked proof of its base case `C = 1`.

The full statement asserts that for every `±1` sequence `f` and every bound `C`
there are `n, d ≥ 1` with `|f d + f (2d) + ⋯ + f (nd)| > C`.  What is proved
here is the case `C = 1`: every `±1` sequence has a homogeneous arithmetic
progression whose sum exceeds `1` in absolute value, witnessed by a progression
of length at most `10`.  Equivalently, no `±1` sequence has discrepancy `≤ 1`. -/
theorem erdos_discrepancy (f : ℕ → ℤ) (hf : IsPMOne f) :
    ∃ n d : ℕ, 0 < n ∧ 0 < d ∧ (1 : ℤ) < |apSum f n d| := by
  obtain ⟨n, d, hn, hd, h⟩ := erdos_discrepancy_base f hf
  exact ⟨n, d, hn, hd, by omega⟩

end Frontier

