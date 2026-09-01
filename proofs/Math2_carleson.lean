/-!
# Carleson
Category: Frontier Math
Target: Math2.carleson
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

open MeasureTheory Filter Topology

variable {T : ℝ} [hT : Fact (0 < T)]

/-- The `N`-th symmetric partial sum of the Fourier series of `f` at `x`. -/
noncomputable def fourierPartialSum (f : AddCircle T → ℂ) (N : ℕ) (x : AddCircle T) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), fourierCoeff f n • fourier n x

/-- The Carleson maximal operator: the supremum over `N` of the moduli of the partial
Fourier sums. -/
noncomputable def carlesonOperator (f : AddCircle T → ℂ) (x : AddCircle T) : ℝ≥0∞ :=
  ⨆ N : ℕ, ‖fourierPartialSum f N x‖ₑ

/-- The weak type `(2,2)` bound for the Carleson maximal operator: this is the analytic heart
of Carleson's theorem (Carleson's inequality), assumed here as a hypothesis. -/
def CarlesonWeakType22 (T : ℝ) [Fact (0 < T)] : Prop :=
  ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (f : Lp ℂ 2 (@haarAddCircle T _)) (lam : ℝ≥0∞), 0 < lam →
    haarAddCircle {x : AddCircle T | lam < carlesonOperator (⇑f) x} ≤
      C * (eLpNorm (⇑f) 2 haarAddCircle / lam) ^ 2

end Math2

