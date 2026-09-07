/-
  Brockian/ConnectivityGoldenBridge.lean — clean packaging of the golden
  algebraic-connectivity facts for the 5-cycle.

  Flagship identity (already proved in Connectivity / Spectral):

      λ₂(C₅)  =  2 − 2 cos(2π/5)  =  2 − 1/φ  =  3 − φ

  where φ = Real.goldenRatio and λ₂ is the second-smallest Laplacian eigenvalue
  of the 2-regular 5-cycle (L = 2I − A, so Laplacian eigenvalues are
  2 − 2 cos(2πk/5)).

  This module does **not** re-prove the analytic identities. It re-exports them
  under connectivity-oriented names and splits the conjunction
  `Connectivity.pentagon_lambda2_phi` into membership / positivity / ordering
  lemmas for downstream use.

  Honesty boundary:
    * C₅ only — no claim about other n beyond the identities cited.
    * No numerology beyond proved φ / cosine identities.
    * Prime-cycle uniqueness of φ − 1 remains `Spectral.golden_unique_to_five`
      (packaged elsewhere in GoldenUniquenessSchema).

  Note: uses `Real.goldenRatio` explicitly (no local `φ` notation) so AXLE
  flatten-attestation does not collide with `Brockian.Core` / Connectivity
  notations.

  Imports (read-only): Connectivity, Spectral, GoldenUniquenessSchema, Geometry.
  Verification (spec §2A): AXLE @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.Connectivity
import Brockian.Spectral
import Brockian.GoldenUniquenessSchema
import Brockian.Geometry

namespace Brockian.ConnectivityGoldenBridge

open Real
open Brockian.Connectivity
open Brockian.Spectral
open Brockian.GoldenUniqueness

/-! ### Substrate: cosine / reciprocal identities

These are pure real identities used by the Laplacian gap. Names stress the
connectivity reading path. -/

/-- **cos(2π/5) = (φ − 1)/2.**  Restatement of `Connectivity.cos_2pi_5`. -/
theorem cos_two_pi_div_five_eq :
    Real.cos (2 * Real.pi / 5) = (Real.goldenRatio - 1) / 2 :=
  Brockian.Connectivity.cos_2pi_5

/-- **1/φ = φ − 1.**  Restatement of `Connectivity.one_div_phi`. -/
theorem inv_phi_eq_phi_sub_one :
    1 / Real.goldenRatio = Real.goldenRatio - 1 :=
  Brockian.Connectivity.one_div_phi

/-- **Adjacency bridge.**  `φ − 1 = 2 cos(2π/5)`.
Restatement of `Spectral.golden_sub_one_eq_two_cos`. -/
theorem golden_sub_one_eq_two_cos :
    Real.goldenRatio - 1 = 2 * Real.cos (2 * Real.pi / 5) :=
  Brockian.Spectral.golden_sub_one_eq_two_cos

/-- **Companion adjacency eigenvalue.**  `2 cos(4π/5) = −φ`.
Restatement of `Spectral.two_cos_four_pi_div_five` / Geometry. -/
theorem two_cos_four_pi_div_five_eq_neg_phi :
    2 * Real.cos (4 * Real.pi / 5) = -Real.goldenRatio :=
  Brockian.Spectral.two_cos_four_pi_div_five

/-- Geometry form of the companion eigenvalue (Core.φ aligned to Mathlib φ). -/
theorem two_cos_four_pi_div_five_geometry :
    2 * Real.cos (4 * Real.pi / 5) = -Real.goldenRatio :=
  Brockian.GoldenUniqueness.golden_ratio_in_C5_geometry

/-! ### The λ₂ identity chain

Three equal real numbers: the circulant Laplacian mode at k = 1,
the golden reciprocal form, and the algebraic rewrite 3 − φ. -/

/-- **Golden connectivity identity.**
`2 − 2 cos(2π/5) = 2 − 1/φ`.
Restatement of `Connectivity.lambda2_eq`. -/
theorem lambda2_eq_two_minus_two_cos :
    2 - 2 * Real.cos (2 * Real.pi / 5) = 2 - 1 / Real.goldenRatio :=
  Brockian.Connectivity.lambda2_eq

/-- Oriented the other way: the golden form equals the cosine form. -/
theorem lambda2_eq_cos_form :
    2 - 1 / Real.goldenRatio = 2 - 2 * Real.cos (2 * Real.pi / 5) :=
  lambda2_eq_two_minus_two_cos.symm

/-- **Three-term chain.**  Via `1/φ = φ − 1` one has `2 − 1/φ = 2 − (φ − 1) = 3 − φ`. -/
theorem lambda2_eq_three_minus_phi :
    2 - 1 / Real.goldenRatio = 3 - Real.goldenRatio := by
  rw [inv_phi_eq_phi_sub_one]
  ring

/-- Same gap written as `2 − (φ − 1)` (adjacency-mode shift of the fundamental mode). -/
theorem lambda2_eq_two_minus_phi_sub_one :
    2 - 1 / Real.goldenRatio = 2 - (Real.goldenRatio - 1) := by
  rw [inv_phi_eq_phi_sub_one]

/-- Full algebraic packaging of the three equal expressions for λ₂(C₅). -/
theorem lambda2_triple_identity :
    2 - 2 * Real.cos (2 * Real.pi / 5) = 2 - 1 / Real.goldenRatio ∧
    2 - 1 / Real.goldenRatio = 3 - Real.goldenRatio ∧
    Real.goldenRatio - 1 = 2 * Real.cos (2 * Real.pi / 5) :=
  ⟨lambda2_eq_two_minus_two_cos, lambda2_eq_three_minus_phi, golden_sub_one_eq_two_cos⟩

/-- Schema-layer restatement (GoldenUniqueness packaging of the same cosine identity). -/
theorem algebraic_connectivity_schema :
    2 - 2 * Real.cos (2 * Real.pi / 5) = 2 - 1 / Real.goldenRatio :=
  Brockian.GoldenUniqueness.algebraic_connectivity_C5_eq

/-! ### Large companion eigenvalue (k = 2,3)

The other nonzero Laplacian value of C₅ is `2 − 2 cos(4π/5) = 2 + φ`. -/

/-- **Large Laplacian eigenvalue of C₅.**  `2 − 2 cos(4π/5) = 2 + φ`. -/
theorem large_eig_eq_two_plus_phi :
    2 - 2 * Real.cos (4 * Real.pi / 5) = 2 + Real.goldenRatio := by
  have h : 2 * Real.cos (4 * Real.pi / 5) = -Real.goldenRatio :=
    two_cos_four_pi_div_five_eq_neg_phi
  linarith

/-! ### Positivity and ordering (split from `pentagon_lambda2_phi`)

`Connectivity.pentagon_lambda2_phi` packages membership + positivity + ordering
as one conjunction. Downstream readers often need the pieces separately. -/

/-- **Membership.**  `2 − 1/φ` is a Laplacian eigenvalue of C₅. -/
theorem lambda2_mem_laplacianEigs5 :
    (2 - 1 / Real.goldenRatio) ∈ laplacianEigs5 :=
  (Brockian.Connectivity.pentagon_lambda2_phi).1

/-- **Positivity.**  The algebraic connectivity is strictly positive:
`0 < 2 − 1/φ`.  (Hence it is the smallest *nonzero* Laplacian eigenvalue.) -/
theorem lambda2_pos : 0 < 2 - 1 / Real.goldenRatio :=
  (Brockian.Connectivity.pentagon_lambda2_phi).2.1

/-- **Ordering.**  The golden gap is ≤ the companion large eigenvalue:
`2 − 1/φ ≤ 2 − 2 cos(4π/5)` (= `2 + φ`). -/
theorem lambda2_le_large_eig :
    (2 - 1 / Real.goldenRatio) ≤ 2 - 2 * Real.cos (4 * Real.pi / 5) :=
  (Brockian.Connectivity.pentagon_lambda2_phi).2.2

/-- Ordering rewritten with the closed form `2 + φ`. -/
theorem lambda2_le_two_plus_phi :
    2 - 1 / Real.goldenRatio ≤ 2 + Real.goldenRatio := by
  have h := lambda2_le_large_eig
  rwa [large_eig_eq_two_plus_phi] at h

/-- **Full algebraic-connectivity package for C₅.**
Membership + positivity + ordering — restatement of `Connectivity.pentagon_lambda2_phi`. -/
theorem algebraic_connectivity_C5 :
    (2 - 1 / Real.goldenRatio) ∈ laplacianEigs5 ∧
    0 < 2 - 1 / Real.goldenRatio ∧
    (2 - 1 / Real.goldenRatio) ≤ 2 - 2 * Real.cos (4 * Real.pi / 5) :=
  Brockian.Connectivity.pentagon_lambda2_phi

/-- Schema-layer packaging of the same three facts. -/
theorem algebraic_connectivity_C5_schema :
    (2 - 1 / Real.goldenRatio) ∈ laplacianEigs5 ∧
    0 < 2 - 1 / Real.goldenRatio ∧
    (2 - 1 / Real.goldenRatio) ≤ 2 - 2 * Real.cos (4 * Real.pi / 5) :=
  Brockian.GoldenUniqueness.algebraic_connectivity_C5_props

/-! ### Degree-normalized ratio

Companion of the gap under 2-regular normalization. -/

/-- **Normalized gap.**  `(2 − 1/φ)/2 = 1 − 1/(2φ)`.
Restatement of `Connectivity.pentagon_ratio`. -/
theorem lambda2_over_degree :
    (2 - 1 / Real.goldenRatio) / 2 = 1 - 1 / (2 * Real.goldenRatio) :=
  Brockian.Connectivity.pentagon_ratio

/-! ### Adjacency spectrum hooks (for the L = 2I − A reading)

The fundamental adjacency mode is φ − 1 = 2 cos(2π/5); Laplacian shifts it by 2. -/

/-- **Fundamental adjacency mode of C₅.**  `φ − 1 ∈ cycleSpectrum 5`. -/
theorem golden_sub_one_mem_adjacency_C5 :
    (Real.goldenRatio - 1) ∈ cycleSpectrum 5 :=
  Brockian.Spectral.golden_in_cycleSpectrum_five

/-- **Companion adjacency mode of C₅.**  `−φ ∈ cycleSpectrum 5`. -/
theorem neg_phi_mem_adjacency_C5 :
    (-Real.goldenRatio) ∈ cycleSpectrum 5 :=
  Brockian.Spectral.neg_golden_in_C5_spectrum

/-- Laplacian gap from the adjacency mode: `2 − (φ − 1) = 2 − 1/φ`. -/
theorem laplacian_gap_from_adjacency_mode :
    2 - (Real.goldenRatio - 1) = 2 - 1 / Real.goldenRatio :=
  lambda2_eq_two_minus_phi_sub_one.symm

end Brockian.ConnectivityGoldenBridge
