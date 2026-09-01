/-
# Boundary Term Vanishes
Category: Gate1 Operator
Target: Brockian.DilationGenerator.boundary_term_vanishes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

/-- A function with compact support contained in `(0, ∞)` vanishes on a neighbourhood
of `0` (indeed on the whole of `(-∞, a)` for some `a > 0`). -/
theorem eventually_eq_zero_near_zero {f : ℝ → ℂ} (hf : HasCompactSupport f)
    (hsupp : tsupport f ⊆ Set.Ioi 0) : ∃ a > 0, ∀ x < a, f x = 0 := by
  rcases Set.eq_empty_or_nonempty (tsupport f) with h | h
  · exact ⟨1, one_pos, fun x _ => image_eq_zero_of_notMem_tsupport (by simp [h])⟩
  · refine ⟨sInf (tsupport f), hsupp (hf.sInf_mem h), fun x hx => ?_⟩
    refine image_eq_zero_of_notMem_tsupport (fun hmem => ?_)
    exact absurd (csInf_le hf.bddBelow hmem) (not_le.mpr hx)

/-- A function with compact support vanishes far out to the right. -/
theorem eventually_eq_zero_atTop {f : ℝ → ℂ} (hf : HasCompactSupport f) :
    ∃ b, ∀ x > b, f x = 0 := by
  obtain ⟨b, hb⟩ := hf.bddAbove
  refine ⟨b, fun x hx => image_eq_zero_of_notMem_tsupport (fun hmem => ?_)⟩
  exact absurd (hb hmem) (not_le.mpr hx)

/-- **Boundary term vanishes.**  For `f, g : ℝ → ℂ` with compact support contained in
`(0, ∞)`, the boundary expression `x * f x * conj (g x)` tends to `0` both as `x → 0⁺`
and as `x → ∞`.  Both limits hold because the expression is identically zero outside a
compact subset of `(0, ∞)`.  The hypotheses on `g` are kept because they are part of the
requested statement, although the argument only needs those on `f`. -/
theorem boundary_term_vanishes {f g : ℝ → ℂ}
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hfs : tsupport f ⊆ Set.Ioi 0) (hgs : tsupport g ⊆ Set.Ioi 0) :
    Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        Filter.atTop (nhds 0) := by
  obtain ⟨a, ha, hazero⟩ := eventually_eq_zero_near_zero hf hfs
  obtain ⟨b, hbzero⟩ := eventually_eq_zero_atTop hf
  constructor
  · refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℂ)))
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ha)] with x hx
    simp [hazero x hx]
  · refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℂ)))
    filter_upwards [Filter.eventually_gt_atTop b] with x hx
    simp [hbzero x hx]

end DilationGenerator
end Brockian

