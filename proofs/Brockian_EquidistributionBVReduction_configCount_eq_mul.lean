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

/-
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Classical

open Filter Finset

namespace Brockian.EquidistributionBVReduction

/-- The number of `n < N` lying in the residue class `r` modulo `q`. -/
noncomputable def residueCount (q r N : ℕ) : ℕ :=
  #{n ∈ Finset.range N | n % q = r % q}

/-- The number of "configurations": pairs `(a, b)` with `a, b < N`, `a ≡ r [MOD q]` and
`b ≡ s [MOD q]`. -/
noncomputable def configCount (q r s N : ℕ) : ℕ :=
  #{p ∈ Finset.range N ×ˢ Finset.range N | p.1 % q = r % q ∧ p.2 % q = s % q}

/-- The expected main term for `configCount q r s N`, namely `(N / q) ^ 2`. -/
noncomputable def mainTerm (q N : ℕ) : ℝ := (N : ℝ) ^ 2 / (q : ℝ) ^ 2

/-- The configuration count factors as a product of two residue counts. -/
lemma configCount_eq_mul (q r s N : ℕ) :
    configCount q r s N = residueCount q r N * residueCount q s N := by
  classical
  rw [configCount, residueCount, residueCount,
    Finset.filter_product (fun a : ℕ => a % q = r % q) (fun b : ℕ => b % q = s % q),
    Finset.card_product]

/-- Two-sided integral bounds for the residue count: `N - r % q ≤ q · count < N - r % q + q`. -/
lemma residueCount_bounds (q r N : ℕ) (hq : 0 < q) :
    (N : ℤ) - ((r % q : ℕ) : ℤ) ≤ (q : ℤ) * (residueCount q r N : ℤ) ∧
      (q : ℤ) * (residueCount q r N : ℤ) < (N : ℤ) - ((r % q : ℕ) : ℤ) + (q : ℤ) := by
  have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hcount := Nat.count_modEq_card_eq_ceil (r := q) (b := N) hq r
  rw [Nat.count_eq_card_filter_range] at hcount
  have hfil : #{n ∈ Finset.range N | n ≡ r [MOD q]} = residueCount q r N := rfl
  rw [hfil] at hcount
  set c : ℕ := residueCount q r N with hc
  set x : ℚ := ((N : ℚ) - ((r % q : ℕ) : ℚ)) / (q : ℚ) with hx
  have hlow : x ≤ (c : ℚ) := by
    have h := Int.le_ceil x
    rw [← hcount] at h
    exact_mod_cast h
  have hhigh : (c : ℚ) < x + 1 := by
    have h := Int.ceil_lt_add_one x
    rw [← hcount] at h
    exact_mod_cast h
  rw [hx, div_le_iff₀ hq'] at hlow
  rw [hx, ← sub_lt_iff_lt_add, lt_div_iff₀ hq'] at hhigh
  constructor
  · have : ((N : ℚ) - ((r % q : ℕ) : ℚ)) ≤ (q : ℚ) * (c : ℚ) := by linarith
    exact_mod_cast this
  · have : (q : ℚ) * (c : ℚ) < (N : ℚ) - ((r % q : ℕ) : ℚ) + (q : ℚ) := by linarith
    exact_mod_cast this

/-- The residue count is within `1` of `N / q`. -/
lemma abs_residueCount_sub_le (q r N : ℕ) (hq : 0 < q) :
    |(residueCount q r N : ℝ) - (N : ℝ) / q| ≤ 1 := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  obtain ⟨hA, hB⟩ := residueCount_bounds q r N hq
  have hA' : (N : ℝ) - ((r % q : ℕ) : ℝ) ≤ (q : ℝ) * (residueCount q r N : ℝ) := by
    exact_mod_cast hA
  have hB' : (q : ℝ) * (residueCount q r N : ℝ) ≤ (N : ℝ) - ((r % q : ℕ) : ℝ) + (q : ℝ) := by
    exact_mod_cast hB.le
  have hrq : ((r % q : ℕ) : ℝ) < (q : ℝ) := by exact_mod_cast Nat.mod_lt _ hq
  have hrq0 : (0 : ℝ) ≤ ((r % q : ℕ) : ℝ) := by positivity
  have hNq : (N : ℝ) / q * (q : ℝ) = (N : ℝ) := by field_simp
  rw [abs_le]
  constructor <;> nlinarith [hq0, hA', hB', hrq, hrq0, hNq]

/-- Each residue class contains `(N / q) · (1 + o(1))` integers below `N`. -/
lemma tendsto_residueCount_div (q r : ℕ) (hq : 0 < q) :
    Tendsto (fun N : ℕ => (residueCount q r N : ℝ) / ((N : ℝ) / q)) atTop (nhds 1) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hbound : ∀ᶠ N : ℕ in atTop,
      ‖(residueCount q r N : ℝ) / ((N : ℝ) / q) - 1‖ ≤ (q : ℝ) / N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have key : (residueCount q r N : ℝ) / ((N : ℝ) / q) - 1
        = ((residueCount q r N : ℝ) - (N : ℝ) / q) / ((N : ℝ) / q) := by
      field_simp
    rw [key, norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (show (0:ℝ) < (N : ℝ) / q by positivity),
      div_le_div_iff₀ (by positivity) hN0]
    have h := abs_residueCount_sub_le q r N hq
    have hqN : (q : ℝ) * ((N : ℝ) / q) = (N : ℝ) := by field_simp
    nlinarith [abs_nonneg ((residueCount q r N : ℝ) - (N : ℝ) / q)]
  have htend : Tendsto (fun N : ℕ => (q : ℝ) / N) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (q : ℝ)
  have h := squeeze_zero_norm' hbound htend
  have h2 := h.add (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ)))
  simpa using h2

/-- **Main result.** For a fixed modulus `q ≥ 1` and residues `r, s`, the number of pairs
`(a, b) ∈ [0, N)^2` with `a ≡ r [MOD q]` and `b ≡ s [MOD q]` is asymptotic to the main term
`N ^ 2 / q ^ 2`. -/
theorem configCount_over_main_tendsto (q r s : ℕ) (hq : 0 < q) :
    Tendsto (fun N : ℕ => (configCount q r s N : ℝ) / mainTerm q N) atTop (nhds 1) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hprod := (tendsto_residueCount_div q r hq).mul (tendsto_residueCount_div q s hq)
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [configCount_eq_mul, mainTerm]
  push_cast
  field_simp

end Brockian.EquidistributionBVReduction

