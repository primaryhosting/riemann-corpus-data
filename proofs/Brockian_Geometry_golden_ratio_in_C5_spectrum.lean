/-
  Brockian/Geometry.lean — the geometric face of the Brockian Pentagonal Law.

  Citation-grade Mathlib-4.32 port of the pentagon / C₅ golden-ratio geometry,
  distilled from the legacy sources `GoldenRatio.lean` and `DihedralGroup.lean`
  (written for ~Mathlib 4.14). Builds on `Brockian.Core` for the φ-algebra.

  Contents:
    * pentagon:  `pentagon_golden_diagonal`  (diagonal = φ · side, via chords)
                 `pentagon_two_distances`     (the two-distance set: {side, diagonal})
    * spectrum:  `golden_ratio_in_C5_spectrum` (−φ = 2cos(4π/5) is a C₅ eigenvalue)
    * dihedral:  `d5_card`  (|D₅| = 10)

  Port-pending (see report): the full `Aut(C₅) ≅ D₅` isomorphism and the flagship
  `golden_unique_to_five` — both rest on `sorry`-laden directions in the legacy
  source and have no clean Mathlib-4.32 witness. They are DROPPED, not faked.

  Verification (spec §2A):  AXLE independent — verified @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.Core

open Brockian.Core

namespace Brockian.Geometry

/-! ### Pentagon: the golden diagonal -/

/-- **Golden diagonal.** In a regular pentagon inscribed in the unit circle, a
diagonal subtends angle `4π/5` and a side subtends `2π/5`; the chord subtending
angle `θ` has length `2 sin(θ/2)`. Hence (diagonal length)/(side length)
`= sin(2π/5) / sin(π/5) = φ`. Stated multiplicatively:
`sin(2π/5) = φ · sin(π/5)`. Discharged via the double-angle identity and
`Brockian.Core.cos_pi_div_five_eq_phi_div_two`. -/
theorem pentagon_golden_diagonal :
    Real.sin (2 * Real.pi / 5) = φ * Real.sin (Real.pi / 5) := by
  have h : (2 * Real.pi / 5) = 2 * (Real.pi / 5) := by ring
  rw [h, Real.sin_two_mul, cos_pi_div_five_eq_phi_div_two]
  ring

/-- **Two-distance property.** A regular pentagon realizes exactly two inter-vertex
distances — the side `2 sin(π/5)` and the diagonal `2 sin(2π/5)` — and they are
distinct, with the diagonal equal to `φ` times the side. -/
theorem pentagon_two_distances :
    Real.sin (2 * Real.pi / 5) = φ * Real.sin (Real.pi / 5) ∧
    Real.sin (Real.pi / 5) ≠ Real.sin (2 * Real.pi / 5) := by
  refine ⟨pentagon_golden_diagonal, ?_⟩
  have hs : 0 < Real.sin (Real.pi / 5) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · nlinarith [Real.pi_pos]
  intro heq
  have hd : Real.sin (2 * Real.pi / 5) = φ * Real.sin (Real.pi / 5) :=
    pentagon_golden_diagonal
  rw [← heq] at hd
  nlinarith [hs, one_lt_phi, hd]

/-! ### The C₅ adjacency spectrum -/

/-- **The golden eigenvalue of C₅.** The adjacency eigenvalues of the 5-cycle are
`2 cos(2πk/5)`, `k = 0,…,4`. At `k = 2` (angle `4π/5`) the eigenvalue is exactly
`−φ`: `2 cos(4π/5) = 2·(−cos(π/5)) = 2·(−φ/2) = −φ`. Thus the golden ratio appears
in the C₅ spectrum. -/
theorem golden_ratio_in_C5_spectrum : 2 * Real.cos (4 * Real.pi / 5) = -φ := by
  have h : (4 * Real.pi / 5) = Real.pi - Real.pi / 5 := by ring
  rw [h, Real.cos_pi_sub, cos_pi_div_five_eq_phi_div_two]
  ring

/-! ### The dihedral symmetry group D₅ -/

/-- **|D₅| = 10.** The dihedral group of the pentagon (5 rotations + 5 reflections)
has order 10 — the ambient symmetry group in which the C₅ automorphisms live.
Ported from `BrockianUniversalLaw.d5_order` / `DihedralGroup.card`. -/
theorem d5_card : Fintype.card (DihedralGroup 5) = 10 := by
  rw [DihedralGroup.card]

end Brockian.Geometry
