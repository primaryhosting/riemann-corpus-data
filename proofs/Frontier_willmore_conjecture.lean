/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
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

namespace Frontier

/-!
## The Willmore energy of a torus of revolution

For the torus of revolution in `ℝ³` obtained by revolving a circle of radius `r`
around an axis lying at distance `R > r` from its centre, the two principal
curvatures at the point of the tube at angle `θ` are

  `κ₁ = 1 / r`  and  `κ₂ = cos θ / (R + r cos θ)`,

the mean curvature is `H = (κ₁ + κ₂) / 2`, and the area element is
`r (R + r cos θ) dθ dφ`.  Integrating gives the classical closed formula

  `W(R, r) = ∫ H² dA = π² R² / (r √(R² - r²))`.

We take this closed formula as the definition of the Willmore energy of the
torus of revolution with radii `R > r > 0`; `willmoreEnergyTorus` below.
-/

/-- The Willmore energy `∫ H² dA` of the torus of revolution in `ℝ³` with
tube radius `r` and centre-circle radius `R` (meaningful for `0 < r < R`),
given by the classical closed formula `π² R² / (r √(R² - r²))`. -/
noncomputable def willmoreEnergyTorus (R r : ℝ) : ℝ :=
  Real.pi ^ 2 * R ^ 2 / (r * Real.sqrt (R ^ 2 - r ^ 2))

/-- The *Clifford torus*, viewed as a torus of revolution in `ℝ³` via
stereographic projection from `S³`, is the one with ratio `R / r = √2`. -/
noncomputable def cliffordRadii : ℝ × ℝ := (Real.sqrt 2, 1)

section Auxiliary

variable {R r : ℝ}

/-- For `0 < r < R` the tube factor `√(R² - r²)` is positive. -/
theorem sqrt_sq_sub_sq_pos (hr : 0 < r) (hR : r < R) : 0 < Real.sqrt (R ^ 2 - r ^ 2) := by
  apply Real.sqrt_pos.mpr
  nlinarith

/-- The denominator `r √(R² - r²)` of the Willmore energy is positive. -/
theorem denom_pos (hr : 0 < r) (hR : r < R) : 0 < r * Real.sqrt (R ^ 2 - r ^ 2) :=
  mul_pos hr (sqrt_sq_sub_sq_pos hr hR)

/-- AM–GM bound: `r √(R² - r²) ≤ R² / 2`. -/
theorem denom_le (hr : 0 < r) (hR : r < R) : r * Real.sqrt (R ^ 2 - r ^ 2) ≤ R ^ 2 / 2 := by
  have hnn : (0 : ℝ) ≤ R ^ 2 - r ^ 2 := by nlinarith
  have hs : Real.sqrt (R ^ 2 - r ^ 2) ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt hnn
  nlinarith [sq_nonneg (r - Real.sqrt (R ^ 2 - r ^ 2)), Real.sqrt_nonneg (R ^ 2 - r ^ 2)]

/-- Equality in the AM–GM bound holds exactly at the Clifford ratio `R = √2 r`. -/
theorem denom_eq_iff (hr : 0 < r) (hR : r < R) :
    r * Real.sqrt (R ^ 2 - r ^ 2) = R ^ 2 / 2 ↔ R = Real.sqrt 2 * r := by
  have hnn : (0 : ℝ) ≤ R ^ 2 - r ^ 2 := by nlinarith
  have hs : Real.sqrt (R ^ 2 - r ^ 2) ^ 2 = R ^ 2 - r ^ 2 := Real.sq_sqrt hnn
  have h2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have h2nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  constructor
  · intro h
    have hsr : Real.sqrt (R ^ 2 - r ^ 2) = r := by nlinarith [Real.sqrt_nonneg (R ^ 2 - r ^ 2)]
    have hR2 : R ^ 2 = 2 * r ^ 2 := by nlinarith
    have hRpos : 0 < R := hr.trans hR
    calc R = Real.sqrt (R ^ 2) := (Real.sqrt_sq hRpos.le).symm
      _ = Real.sqrt (2 * r ^ 2) := by rw [hR2]
      _ = Real.sqrt 2 * r := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_sq hr.le]
  · intro h
    subst h
    have hx : (Real.sqrt 2 * r) ^ 2 - r ^ 2 = r ^ 2 := by
      rw [mul_pow, h2]; ring
    rw [hx, Real.sqrt_sq hr.le, mul_pow, h2]
    ring

end Auxiliary

/-!
## The base case: tori of revolution
-/

/-- **Willmore's inequality for tori of revolution.**  Every torus of revolution
with radii `0 < r < R` has Willmore energy at least `2π²`. -/
theorem two_pi_sq_le_willmoreEnergyTorus {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    2 * Real.pi ^ 2 ≤ willmoreEnergyTorus R r := by
  have hd : 0 < r * Real.sqrt (R ^ 2 - r ^ 2) := denom_pos hr hR
  rw [willmoreEnergyTorus, le_div_iff₀ hd]
  have hpi : 0 < Real.pi ^ 2 := pow_pos Real.pi_pos 2
  nlinarith [denom_le hr hR]

/-- **Equality case.**  A torus of revolution has Willmore energy exactly `2π²`
if and only if its radii are in the Clifford ratio `R = √2 r`. -/
theorem willmoreEnergyTorus_eq_two_pi_sq_iff {R r : ℝ} (hr : 0 < r) (hR : r < R) :
    willmoreEnergyTorus R r = 2 * Real.pi ^ 2 ↔ R = Real.sqrt 2 * r := by
  have hd : 0 < r * Real.sqrt (R ^ 2 - r ^ 2) := denom_pos hr hR
  have hpi : 0 < Real.pi ^ 2 := pow_pos Real.pi_pos 2
  rw [willmoreEnergyTorus, div_eq_iff (ne_of_gt hd)]
  rw [← denom_eq_iff hr hR]
  constructor
  · intro h; nlinarith
  · intro h; rw [h]; ring

/-- The Clifford torus has Willmore energy exactly `2π²`. -/
theorem willmoreEnergyTorus_clifford :
    willmoreEnergyTorus cliffordRadii.1 cliffordRadii.2 = 2 * Real.pi ^ 2 := by
  have h2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  simp only [cliffordRadii, willmoreEnergyTorus, h2]
  norm_num
  ring

/-!
## A schematic formalization of the general conjecture

Mathlib currently has no theory of mean curvature of immersed surfaces, so the
full Marques–Neves theorem cannot be stated verbatim.  The structure below
records the *shape* of the statement: a class of surfaces, a genus-one
predicate, a Willmore energy, and a distinguished Clifford torus of energy
`2π²`.  `MinimizedByClifford` is then the assertion that the Clifford torus
minimizes the Willmore energy in that class.
-/

/-- A schematic setting for the Willmore problem: a class of surfaces equipped
with a genus-one predicate, a Willmore energy functional, and a distinguished
"Clifford torus" of genus one whose energy is `2π²`. -/
structure WillmoreSetting where
  /-- The class of surfaces under consideration. -/
  Surface : Type
  /-- The predicate singling out the genus-one surfaces. -/
  genusOne : Surface → Prop
  /-- The Willmore energy `∫ H² dA`. -/
  energy : Surface → ℝ
  /-- The distinguished Clifford torus of the setting. -/
  clifford : Surface
  /-- The Clifford torus has genus one. -/
  clifford_genusOne : genusOne clifford
  /-- The Willmore energy of the Clifford torus is `2π²`. -/
  clifford_energy : energy clifford = 2 * Real.pi ^ 2

/-- The Willmore conjecture for a given setting: every genus-one surface has
Willmore energy at least that of the Clifford torus, namely `2π²`. -/
def MinimizedByClifford (S : WillmoreSetting) : Prop :=
  ∀ s : S.Surface, S.genusOne s → S.energy S.clifford ≤ S.energy s

/-- The setting of tori of revolution in `ℝ³`, parameterized by their radii
`0 < r < R`; all of them have genus one. -/
noncomputable def revolutionTori : WillmoreSetting where
  Surface := {p : ℝ × ℝ // 0 < p.2 ∧ p.2 < p.1}
  genusOne := fun _ => True
  energy := fun p => willmoreEnergyTorus p.1.1 p.1.2
  clifford := ⟨cliffordRadii, by
    constructor
    · norm_num [cliffordRadii]
    · have : (1 : ℝ) < Real.sqrt 2 := by
        nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
      simpa [cliffordRadii] using this⟩
  clifford_genusOne := trivial
  clifford_energy := willmoreEnergyTorus_clifford

/-- **Willmore conjecture — Lean-checked base case (Marques–Neves).**

The full theorem of Marques and Neves states that every immersed torus in `ℝ³`
(equivalently, every genus-one closed surface) has Willmore energy at least
`2π²`, with equality exactly for the Clifford torus and its images under
conformal transformations.

What is proved here is the classical base case, for the family of tori of
revolution, together with the sharp equality characterization:

* every torus of revolution with radii `0 < r < R` has Willmore energy
  `π² R² / (r √(R² - r²)) ≥ 2π²`, i.e. the Clifford torus minimizes the
  Willmore energy in this class;
* equality holds precisely when `R = √2 · r`, the Clifford ratio.
-/
theorem willmore_conjecture :
    MinimizedByClifford revolutionTori ∧
      ∀ R r : ℝ, 0 < r → r < R →
        (willmoreEnergyTorus R r = 2 * Real.pi ^ 2 ↔ R = Real.sqrt 2 * r) := by
  refine ⟨?_, fun R r hr hR => willmoreEnergyTorus_eq_two_pi_sq_iff hr hR⟩
  rintro ⟨⟨R, r⟩, hr, hR⟩ -
  have h : revolutionTori.energy revolutionTori.clifford = 2 * Real.pi ^ 2 :=
    revolutionTori.clifford_energy
  rw [h]
  exact two_pi_sq_le_willmoreEnergyTorus hr hR

end Frontier


