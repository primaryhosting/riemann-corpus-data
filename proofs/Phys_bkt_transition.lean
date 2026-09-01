import Mathlib

/-!
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
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

set_option grind.warning false

namespace Phys

/-- The Kosterlitz–Thouless transition temperature of the 2D XY model with spin
stiffness (coupling) `J`, in units where the Boltzmann constant is `1`:
`T_BKT = π J / 2`. -/
noncomputable def bktTemperature (J : ℝ) : ℝ := Real.pi * J / 2

/-- Free energy cost `F = E - T S` of inserting a single vortex of core size `a`
into a two-dimensional XY system of linear size `L`.

The energy of an isolated vortex is `E = π J log (L / a)`, and its entropy is
`S = 2 log (L / a)` (there are `(L / a) ^ 2` distinguishable positions for the
core), so `F = (π J - 2 T) log (L / a)`. -/
noncomputable def vortexFreeEnergy (J T L a : ℝ) : ℝ :=
    (Real.pi * J - 2 * T) * Real.log (L / a)

/-- The anomalous exponent governing the algebraic decay
`⟨s(0) · s(r)⟩ ∼ r ^ (-η)` of spin correlations in the low-temperature
(quasi-long-range-ordered) phase of the 2D XY model: `η(T) = T / (2 π J)`. -/
noncomputable def corrExponent (J T : ℝ) : ℝ := T / (2 * Real.pi * J)

/-- The logarithm `log (L / a)` occurring in the vortex free energy is positive
for a system larger than the vortex core. -/
lemma log_ratio_pos {L a : ℝ} (ha : 0 < a) (hL : a < L) : 0 < Real.log (L / a) := by
  have h1 : 1 < L / a := (one_lt_div ha).2 hL
  exact Real.log_pos h1

/-- **Berezinskii–Kosterlitz–Thouless topological phase transition of the 2D XY
model.**

For a two-dimensional XY model with spin stiffness `J > 0`, vortex core size
`a > 0` and linear system size `L > a`, the single-vortex free energy
`F(T) = (π J - 2 T) log (L / a)` changes sign exactly at the BKT temperature
`T_BKT = π J / 2`:

* for `T < T_BKT` the free energy cost of a free vortex is strictly positive, so
  isolated vortices are suppressed (bound vortex–antivortex pairs, topologically
  ordered / quasi-long-range-ordered phase);
* at `T = T_BKT` the cost vanishes;
* for `T > T_BKT` the cost is strictly negative, so free vortices proliferate and
  destroy quasi-long-range order (disordered phase).

Moreover `F` is strictly decreasing in `T`, the transition temperature is
strictly positive, and at the transition the spin-correlation exponent takes the
universal value `η(T_BKT) = 1/4`, equivalently the reduced stiffness jumps by the
universal amount `J / T_BKT = 2 / π`. -/
theorem bkt_transition (J a L : ℝ) (hJ : 0 < J) (ha : 0 < a) (hL : a < L) :
    (0 < bktTemperature J) ∧
    (∀ T : ℝ, T < bktTemperature J → 0 < vortexFreeEnergy J T L a) ∧
    (vortexFreeEnergy J (bktTemperature J) L a = 0) ∧
    (∀ T : ℝ, bktTemperature J < T → vortexFreeEnergy J T L a < 0) ∧
    (StrictAnti fun T : ℝ => vortexFreeEnergy J T L a) ∧
    (corrExponent J (bktTemperature J) = 1 / 4) ∧
    (J / bktTemperature J = 2 / Real.pi) := by
  have hlog : 0 < Real.log (L / a) := log_ratio_pos ha hL
  have hpi : 0 < Real.pi := Real.pi_pos
  refine ⟨by unfold bktTemperature; positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hT
    have h : 0 < Real.pi * J - 2 * T := by
      unfold bktTemperature at hT; linarith
    exact mul_pos h hlog
  · unfold vortexFreeEnergy bktTemperature
    have : Real.pi * J - 2 * (Real.pi * J / 2) = 0 := by ring
    rw [this, zero_mul]
  · intro T hT
    have h : Real.pi * J - 2 * T < 0 := by
      unfold bktTemperature at hT; linarith
    exact mul_neg_of_neg_of_pos h hlog
  · intro T₁ T₂ h
    have : (Real.pi * J - 2 * T₂) < (Real.pi * J - 2 * T₁) := by linarith
    exact mul_lt_mul_of_pos_right this hlog
  · unfold corrExponent bktTemperature
    field_simp
    ring
  · unfold bktTemperature
    field_simp

end Phys

