import Mathlib

/-!
# Boundary Term Vanishes
Category: Gate1 Operator
Target: Brockian.DilationGenerator.boundary_term_vanishes
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
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

open Filter Topology

namespace Brockian
namespace DilationGenerator

/-- **Vanishing of the boundary term for the dilation generator.**

For `f g : ℝ → ℂ` with compact support contained in `(0, ∞)`, the boundary expression
`x * f x * conj (g x)` tends to `0` both as `x → 0⁺` and as `x → +∞`.

Near `0` the point `0` lies outside the closed set `tsupport f`, so `f` vanishes on a whole
neighbourhood of `0`; near `+∞` the set `tsupport f` is bounded above, so `f` vanishes for all
large `x`. In both cases the product is eventually identically `0`.

The hypotheses `hg` and `hg0` on `g` are part of the requested statement; the proof only needs
the corresponding hypotheses on `f`. -/
theorem boundary_term_vanishes
    (f g : ℝ → ℂ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hf0 : tsupport f ⊆ Set.Ioi 0) (hg0 : tsupport g ⊆ Set.Ioi 0) :
    Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * starRingEnd ℂ (g x))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
    ∧ Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * starRingEnd ℂ (g x))
        Filter.atTop (nhds 0) := by
  have h0 : (0 : ℝ) ∉ tsupport f := fun h => by simpa using hf0 h
  constructor
  · -- Near `0⁺`: `f` vanishes on the open complement of `tsupport f`, a neighbourhood of `0`.
    apply Filter.Tendsto.congr' (f₁ := fun _ : ℝ => (0 : ℂ)) _ tendsto_const_nhds
    filter_upwards [nhdsWithin_le_nhds
      ((isClosed_tsupport f).isOpen_compl.mem_nhds h0)] with x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  · -- At `+∞`: `tsupport f` is compact, hence bounded above, so `f` vanishes for large `x`.
    obtain ⟨R, hR⟩ := (hf : IsCompact (tsupport f)).bddAbove
    apply Filter.Tendsto.congr' (f₁ := fun _ : ℝ => (0 : ℂ)) _ tendsto_const_nhds
    filter_upwards [Filter.eventually_gt_atTop R] with x hx
    have hxn : x ∉ tsupport f := fun h => absurd (hR h) (not_le.mpr hx)
    simp [image_eq_zero_of_notMem_tsupport hxn]

end DilationGenerator
end Brockian

