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

namespace Math

/-- **Bolzano–Weierstrass in ℝⁿ**: every bounded sequence in `ℝ^n` (here modelled as
`EuclideanSpace ℝ (Fin n)`) admits a subsequence converging to some point. -/
theorem bolzano_weierstrass (n : ℕ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hb : ∃ C : ℝ, ∀ k, ‖x k‖ ≤ C) :
    ∃ (g : ℕ → ℕ) (L : EuclideanSpace ℝ (Fin n)),
      StrictMono g ∧ Filter.Tendsto (x ∘ g) Filter.atTop (nhds L) := by
  obtain ⟨C, hC⟩ := hb
  have hcpt : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) C) :=
    isCompact_closedBall _ _
  have hmem : ∀ k, x k ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) C := by
    intro k
    simpa [Metric.mem_closedBall, dist_eq_norm] using hC k
  obtain ⟨L, _, g, hg, htend⟩ := hcpt.tendsto_subseq hmem
  exact ⟨g, L, hg, htend⟩

end Math

