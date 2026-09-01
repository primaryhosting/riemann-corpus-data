import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real Filter Topology

namespace Math2

open scoped Classical

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) · sin²θ`.
The associated measure `(2/π) sin²θ dθ` on `[0, π]` is the Sato–Tate measure. -/
noncomputable def satoTateDensity (θ : ℝ) : ℝ := (2 / Real.pi) * Real.sin θ ^ 2

/-- The Frobenius angle attached to a prime `p` and the trace of Frobenius `a`:
the unique `θ ∈ [0, π]` with `a = 2√p · cos θ` (the Hasse bound `|a| ≤ 2√p`
guarantees that this is well defined). -/
noncomputable def frobeniusAngle (p : ℕ) (a : ℤ) : ℝ :=
  Real.arccos ((a : ℝ) / (2 * Real.sqrt p))

/-- The proportion, among the primes `p < N`, of those whose Frobenius angle lies in
`[α, β]`. -/
noncomputable def angleRatio (a : ℕ → ℤ) (α β : ℝ) (N : ℕ) : ℝ :=
  (((Finset.range N).filter
      (fun p => Nat.Prime p ∧ frobeniusAngle p (a p) ∈ Set.Icc α β)).card : ℝ) /
    (((Finset.range N).filter Nat.Prime).card : ℝ)

/-- The Sato–Tate equidistribution property for a sequence `a : ℕ → ℤ` of traces of
Frobenius: for every subinterval `[α, β] ⊆ [0, π]`, the proportion of primes whose
Frobenius angle lies in `[α, β]` converges to the Sato–Tate measure of `[α, β]`.

The Sato–Tate conjecture (a theorem of Clozel–Harris–Shepherd-Barron–Taylor for
elliptic curves over `ℚ`) asserts that this holds for the trace sequence of any
elliptic curve without complex multiplication. -/
def SatoTateEquidistributed (a : ℕ → ℤ) : Prop :=
  ∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ Real.pi →
    Tendsto (angleRatio a α β) atTop (𝓝 (∫ θ in α..β, satoTateDensity θ))

/-- The Sato–Tate density integrates to `1` over `[0, π]`, i.e. `(2/π) sin²θ dθ` is a
probability measure on `[0, π]`. -/
theorem integral_satoTateDensity : (∫ θ in (0:ℝ)..Real.pi, satoTateDensity θ) = 1 := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [satoTateDensity]
  rw [intervalIntegral.integral_const_mul, integral_sin_sq]
  field_simp
  simp

/-- **The Sato–Tate distribution of Frobenius angles.**

Let `a : ℕ → ℤ` be the trace-of-Frobenius sequence of an elliptic curve over `ℚ`
(so `a p = p + 1 - #E(𝔽_p)` at a prime `p` of good reduction), subject to the Hasse
bound `|a p| ≤ 2√p`, and assume the curve has no complex multiplication, so that its
Frobenius angles are Sato–Tate equidistributed. Then:

* each Frobenius angle `θ p = arccos (a p / (2√p))` lies in `[0, π]`;
* it is the genuine Frobenius angle, i.e. `a p = 2√p · cos (θ p)`;
* the Sato–Tate density `(2/π) sin²θ` is a probability density on `[0, π]`;
* consequently the angles are distributed on `[0, π]` according to the Sato–Tate
  measure, the total mass being `1`.
-/
theorem sato_tate (a : ℕ → ℤ) (hHasse : ∀ p : ℕ, p.Prime → |(a p : ℝ)| ≤ 2 * Real.sqrt p)
    (hST : SatoTateEquidistributed a) :
    (∀ p : ℕ, frobeniusAngle p (a p) ∈ Set.Icc 0 Real.pi) ∧
    (∀ p : ℕ, p.Prime → 2 * Real.sqrt p * Real.cos (frobeniusAngle p (a p)) = (a p : ℝ)) ∧
    (∀ θ : ℝ, 0 ≤ satoTateDensity θ) ∧
    (∫ θ in (0:ℝ)..Real.pi, satoTateDensity θ) = 1 ∧
    (∀ α β : ℝ, 0 ≤ α → α ≤ β → β ≤ Real.pi →
      Tendsto (angleRatio a α β) atTop (𝓝 (∫ θ in α..β, satoTateDensity θ))) ∧
    Tendsto (angleRatio a 0 Real.pi) atTop (𝓝 1) := by
  refine ⟨fun p => ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩, ?_, ?_,
    integral_satoTateDensity, hST, ?_⟩
  · intro p hp
    have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
    have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
    have hne : (2 * Real.sqrt p) ≠ 0 := by positivity
    have habs : |(a p : ℝ) / (2 * Real.sqrt p)| ≤ 1 := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.sqrt p),
        div_le_one (by positivity)]
      exact hHasse p hp
    have := abs_le.mp habs
    rw [frobeniusAngle, Real.cos_arccos this.1 this.2]
    field_simp
  · intro θ
    have h : (0:ℝ) ≤ 2 / Real.pi := by positivity
    exact mul_nonneg h (sq_nonneg _)
  · have := hST 0 Real.pi le_rfl Real.pi_nonneg le_rfl
    rwa [integral_satoTateDensity] at this

end Math2

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

