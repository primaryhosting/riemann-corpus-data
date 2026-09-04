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

open Filter Topology

namespace Brockian.DilationGenerator

/-- **Boundary term vanishes.**

For `f g : ℝ → ℂ` with compact support contained in `(0, ∞)`, the boundary expression
`x * f x * conj (g x)` tends to `0` both as `x → 0⁺` and as `x → +∞`.

Both limits hold because the expression is *identically zero* outside a compact subset of
`(0, ∞)`: near `0` because `0` is not in the (closed) support of `f`, and near `+∞` because the
support of `f` is bounded above.

Smoothness of `f` and `g` is not needed. The hypotheses `hg`, `hg0` on `g` were requested in the
statement but are not needed for the proof either: the vanishing of `f` alone kills the product.
-/
theorem boundary_term_vanishes
    (f g : ℝ → ℂ)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hf0 : tsupport f ⊆ Set.Ioi (0 : ℝ)) (hg0 : tsupport g ⊆ Set.Ioi (0 : ℝ)) :
    Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0)
      ∧ Filter.Tendsto (fun x : ℝ => (x : ℂ) * f x * (starRingEnd ℂ) (g x))
        Filter.atTop (nhds 0) := by
  have hzero : ∀ x : ℝ, x ∉ tsupport f → (x : ℂ) * f x * (starRingEnd ℂ) (g x) = 0 := by
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport hx]
    ring
  constructor
  · -- Near `0⁺`: `0` lies in the open complement of the closed set `tsupport f`.
    have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
    have h0 : (0 : ℝ) ∈ (tsupport f)ᶜ := fun h => absurd (hf0 h) (by simp)
    have hev : ∀ᶠ x : ℝ in nhds (0 : ℝ), (x : ℂ) * f x * (starRingEnd ℂ) (g x) = 0 := by
      filter_upwards [hopen.mem_nhds h0] with x hx using hzero x hx
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [hev.filter_mono nhdsWithin_le_nhds] with x hx using hx.symm
  · -- Near `+∞`: `tsupport f` is compact, hence bounded above.
    obtain ⟨M, hM⟩ := hf.isCompact.bddAbove
    refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_gt_atTop M] with x hx
    exact (hzero x (fun hmem => absurd (hM hmem) (by linarith))).symm

end Brockian.DilationGenerator

