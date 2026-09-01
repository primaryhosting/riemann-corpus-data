import Mathlib
/-!
# Heine Borel
Category: Pure Mathematics
Target: Math.heine_borel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Math

/-- **Heine–Borel theorem** for `ℝ^n` (modelled as `EuclideanSpace ℝ (Fin n)`):
a subset of `ℝ^n` is compact if and only if it is closed and bounded.

This is `Metric.isCompact_iff_isClosed_bounded`, which applies since `EuclideanSpace ℝ (Fin n)`
is a proper (finite-dimensional real normed) metric space. -/
theorem heine_borel {n : ℕ} (s : Set (EuclideanSpace ℝ (Fin n))) :
    IsCompact s ↔ IsClosed s ∧ Bornology.IsBounded s :=
  Metric.isCompact_iff_isClosed_bounded

/-- Heine–Borel for `ℝ^n` with boundedness spelled out as a uniform bound on the norm. -/
theorem heine_borel' {n : ℕ} (s : Set (EuclideanSpace ℝ (Fin n))) :
    IsCompact s ↔ IsClosed s ∧ ∃ C : ℝ, ∀ x ∈ s, ‖x‖ ≤ C := by
  rw [heine_borel, isBounded_iff_forall_norm_le]

/-- Heine–Borel for the product model `Fin n → ℝ` of `ℝ^n`. -/
theorem heine_borel_pi {n : ℕ} (s : Set (Fin n → ℝ)) :
    IsCompact s ↔ IsClosed s ∧ Bornology.IsBounded s :=
  Metric.isCompact_iff_isClosed_bounded

end Math

