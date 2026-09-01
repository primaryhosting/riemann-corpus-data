import Frontier.Spectral.CycleGapObstruction

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
# NEGATIVE / OBSTRUCTION RESULT: the cycle spectral gap vanishes

This module proves an **honest negative result** about the explicit family of
real Fourier eigenvalues of ordinary (unweighted, undirected) cycle graphs:

  `cycleEigenvalue n k = 2 - 2 * Real.cos (2 * π * k / n)`,  `k : Fin n`.

Contents:

* `cycleEigenvalue_zero`      : the eigenvalue at `k = 0` is `0`;
* `cycleEigenvalue_pos`       : all other eigenvalues are strictly positive;
* `cycleEigenvalue_gap_le`, `cycleEigenvalue_isLeast` :
    the *least positive* eigenvalue is exactly
    `cycleGapFormula n = 2 - 2 * cos (2 * π / n)` — a genuine minimality
    theorem quantified over all `k ≠ 0`, not a definitional shortcut;
* `cycleGapFormula_tendsto_zero`, `exists_cycle_gap_lt`,
  `no_uniform_positive_cycle_gap` :
    the gap tends to `0`, so **no uniform positive lower bound** on the gap
    holds across all cycles.

**Scope disclaimer.** Everything below concerns *only* this explicit cycle
eigenvalue family; nothing is claimed about any other graph or operator family.
The result is an OBSTRUCTION: it falsifies any strategy that hopes to obtain a
uniform spectral gap from plain cycle graphs, and identifies the need for a
genuinely expanding (or otherwise modified) family of graphs.
-/
import Mathlib

open Filter Topology

namespace Frontier.Spectral

/-- The `k`-th real Fourier eigenvalue of the cycle graph on `n` vertices:
`2 - 2 cos (2π k / n)`. -/
noncomputable def cycleEigenvalue (n : ℕ) (k : Fin n) : ℝ :=
  2 - 2 * Real.cos (2 * Real.pi * (k : ℝ) / (n : ℝ))

/-- The closed-form spectral gap of the cycle graph on `n` vertices. -/
noncomputable def cycleGapFormula (n : ℕ) : ℝ :=
  2 - 2 * Real.cos (2 * Real.pi / (n : ℝ))

/-! ### Basic values -/

/-- The trivial mode `k = 0` has eigenvalue `0`. -/
theorem cycleEigenvalue_zero (n : ℕ) (hn : 0 < n) :
    cycleEigenvalue n (⟨0, hn⟩ : Fin n) = 0 := by
  simp [cycleEigenvalue]

/-- The eigenvalue at index `1` is exactly the gap formula. -/
theorem cycleEigenvalue_one (n : ℕ) (hn : 1 < n) :
    cycleEigenvalue n (⟨1, hn⟩ : Fin n) = cycleGapFormula n := by
  simp [cycleEigenvalue, cycleGapFormula]

/-! ### Elementary bounds on the angle `2π k / n` -/

section Angle

variable {n : ℕ}

private lemma angle_lower (hn : 3 ≤ n) (k : Fin n) (hk : (k : ℕ) ≠ 0) :
    2 * Real.pi / (n : ℝ) ≤ 2 * Real.pi * (k : ℝ) / (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ (k : ℕ) := by
    have : 1 ≤ (k : ℕ) := Nat.one_le_iff_ne_zero.mpr hk
    exact_mod_cast this
  have hpi := Real.pi_pos
  refine (div_le_div_iff_of_pos_right hn0).mpr ?_
  nlinarith

private lemma angle_upper (hn : 3 ≤ n) (k : Fin n) :
    2 * Real.pi * (k : ℝ) / (n : ℝ) ≤ 2 * Real.pi - 2 * Real.pi / (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hkn : ((k : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
    have : (k : ℕ) + 1 ≤ n := k.isLt
    exact_mod_cast this
  have hpi := Real.pi_pos
  rw [div_le_iff₀ hn0]
  have hrw : (2 * Real.pi - 2 * Real.pi / (n : ℝ)) * (n : ℝ)
      = 2 * Real.pi * (n : ℝ) - 2 * Real.pi := by
    field_simp
  rw [hrw]
  nlinarith

private lemma angle_pos (hn : 3 ≤ n) : 0 < 2 * Real.pi / (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have := Real.pi_pos
  positivity

private lemma angle_le_pi (hn : 3 ≤ n) : 2 * Real.pi / (n : ℝ) ≤ Real.pi := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by
    have : 2 ≤ n := by omega
    exact_mod_cast this
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have := Real.pi_pos
  rw [div_le_iff₀ hn0]
  nlinarith

end Angle

/-! ### Positivity of the nontrivial eigenvalues -/

/-- Every nonzero Fourier mode of the cycle has strictly positive eigenvalue. -/
theorem cycleEigenvalue_pos (n : ℕ) (hn : 3 ≤ n) (k : Fin n) (hk : (k : ℕ) ≠ 0) :
    0 < cycleEigenvalue n k := by
  set θ : ℝ := 2 * Real.pi * (k : ℝ) / (n : ℝ) with hθ
  have hlb : 0 < θ := lt_of_lt_of_le (angle_pos hn) (angle_lower hn k hk)
  have hub : θ < 2 * Real.pi := by
    have := angle_upper hn k
    have := angle_pos (n := n) hn
    linarith
  have hne : Real.cos θ ≠ 1 := by
    intro h
    have := (Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) hub).mp h
    linarith
  have hle : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have : Real.cos θ < 1 := lt_of_le_of_ne hle hne
  simp only [cycleEigenvalue, ← hθ]
  linarith

/-- Restatement of `cycleEigenvalue_pos` with the index compared to the zero
element of `Fin n` directly. -/
theorem cycleEigenvalue_pos' (n : ℕ) (hn : 3 ≤ n) (k : Fin n)
    (hk : k ≠ (⟨0, by omega⟩ : Fin n)) : 0 < cycleEigenvalue n k :=
  cycleEigenvalue_pos n hn k (by simpa [Fin.ext_iff] using hk)

/-! ### Minimality: the gap formula is the least positive eigenvalue -/

/-- Key trigonometric comparison: for `1 ≤ k ≤ n - 1`, the cosine of the mode
angle is at most the cosine of the first mode angle. -/
theorem cos_mode_le_cos_first (n : ℕ) (hn : 3 ≤ n) (k : Fin n) (hk : (k : ℕ) ≠ 0) :
    Real.cos (2 * Real.pi * (k : ℝ) / (n : ℝ)) ≤ Real.cos (2 * Real.pi / (n : ℝ)) := by
  set a : ℝ := 2 * Real.pi / (n : ℝ) with ha
  set θ : ℝ := 2 * Real.pi * (k : ℝ) / (n : ℝ) with hθ
  have ha0 : 0 < a := angle_pos hn
  have hlb : a ≤ θ := angle_lower hn k hk
  have hub : θ ≤ 2 * Real.pi - a := angle_upper hn k
  rcases le_or_gt θ Real.pi with h | h
  · exact Real.cos_le_cos_of_nonneg_of_le_pi ha0.le h hlb
  · have hsym : Real.cos θ = Real.cos (2 * Real.pi - θ) := by
      rw [Real.cos_two_pi_sub]
    rw [hsym]
    exact Real.cos_le_cos_of_nonneg_of_le_pi ha0.le (by linarith) (by linarith)

/-- **Minimality theorem.** The gap formula lower-bounds every nontrivial
eigenvalue of the cycle. -/
theorem cycleGapFormula_le_cycleEigenvalue (n : ℕ) (hn : 3 ≤ n) (k : Fin n)
    (hk : (k : ℕ) ≠ 0) : cycleGapFormula n ≤ cycleEigenvalue n k := by
  have := cos_mode_le_cos_first n hn k hk
  simp only [cycleGapFormula, cycleEigenvalue]
  linarith

/-- **Least positive value.** The set of eigenvalues of nonzero Fourier modes of
the cycle on `n ≥ 3` vertices has least element `cycleGapFormula n`, which is
attained at the mode `k = 1`. -/
theorem cycleEigenvalue_isLeast (n : ℕ) (hn : 3 ≤ n) :
    IsLeast {x : ℝ | ∃ k : Fin n, (k : ℕ) ≠ 0 ∧ cycleEigenvalue n k = x}
      (cycleGapFormula n) := by
  constructor
  · exact ⟨⟨1, by omega⟩, by simp, cycleEigenvalue_one n (by omega)⟩
  · rintro x ⟨k, hk, rfl⟩
    exact cycleGapFormula_le_cycleEigenvalue n hn k hk

/-- The gap formula is itself positive for `n ≥ 3`. -/
theorem cycleGapFormula_pos (n : ℕ) (hn : 3 ≤ n) : 0 < cycleGapFormula n := by
  have h := cycleEigenvalue_pos n hn ⟨1, by omega⟩ (by simp)
  rwa [cycleEigenvalue_one n (by omega)] at h

/-! ### The gap tends to zero -/

/-- The cycle spectral gap tends to `0` as the number of vertices tends to
infinity. -/
theorem cycleGapFormula_tendsto_zero :
    Tendsto cycleGapFormula atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => 2 * Real.pi / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h2 : Tendsto (fun n : ℕ => Real.cos (2 * Real.pi / (n : ℝ))) atTop (𝓝 1) := by
    have := (Real.continuous_cos.tendsto (0 : ℝ)).comp h1
    simpa [Function.comp] using this
  have h3 : Tendsto (fun n : ℕ => 2 - 2 * Real.cos (2 * Real.pi / (n : ℝ))) atTop
      (𝓝 (2 - 2 * 1)) := tendsto_const_nhds.sub (h2.const_mul 2)
  simpa [cycleGapFormula] using h3

/-! ### The obstruction -/

/-- (a) For every `ε > 0` there is a cycle with at least three vertices whose
spectral gap is smaller than `ε`. -/
theorem exists_cycle_gap_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 3 ≤ n ∧ cycleGapFormula n < ε := by
  have h := cycleGapFormula_tendsto_zero
  have hev : ∀ᶠ n : ℕ in atTop, cycleGapFormula n < ε := by
    have := h (Iio_mem_nhds hε)
    simpa [Set.preimage] using this
  obtain ⟨N, hN⟩ := (hev.and (eventually_ge_atTop 3)).exists
  exact ⟨N, hN.2, hN.1⟩

/-- (b) **NEGATIVE / OBSTRUCTION RESULT.** There is no uniform positive lower
bound for the spectral gaps of the ordinary cycle graphs: no `ε > 0` satisfies
`ε ≤ cycleGapFormula n` for all `n ≥ 3`.

Consequently any construction aiming at a uniform spectral gap cannot be based
on plain cycles; a genuinely expanding (or otherwise modified) family is
required. -/
theorem no_uniform_positive_cycle_gap :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, 3 ≤ n → ε ≤ cycleGapFormula n := by
  rintro ⟨ε, hε, hbound⟩
  obtain ⟨n, hn3, hlt⟩ := exists_cycle_gap_lt hε
  exact absurd (hbound n hn3) (not_le.mpr hlt)

#print axioms no_uniform_positive_cycle_gap

end Frontier.Spectral

