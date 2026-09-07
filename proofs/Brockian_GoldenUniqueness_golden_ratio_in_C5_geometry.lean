/-
  Brockian/GoldenUniquenessSchema.lean — reusable packaging of golden_unique_to_five.

  Schema (PROVED, no numerology, no cosmic overclaim):

    Layer A — algebraic identity (no primality, no cycle graphs):
      φ − 1 = 2 cos(2π/5) = 1/φ, and the companion −φ = 2 cos(4π/5).

    Layer B — C₅ specialization (membership only):
      φ − 1 and −φ lie in the concrete cycle spectrum of C₅.

    Layer C — prime rigidity (exactly the flagship iff):
      for prime p, (φ − 1) ∈ cycleSpectrum p  ↔  p = 5.
      Corollary: if p is prime and p ≠ 5, then φ − 1 ∉ cycleSpectrum p.

  Honesty boundary: this module restates and factors `Brockian.Spectral.golden_unique_to_five`.
  It does NOT claim that only five is “cosmic,” that non-prime n cannot carry φ − 1,
  or that C₅ is unique among all n ∈ ℕ. The prime-cycle biconditional is the full claim.

  Contents:
    * algebraic: golden_sub_one_eq_two_cos, inv_golden_eq_sub_one, two_cos_links
    * C₅: golden_mem_C5, neg_golden_mem_C5, two_cos_fundamental_mode_C5
    * rigidity: golden_unique_to_five (restate), golden_not_in_prime_cycle_ne_five
    * optional Laplacian bridge: algebraic_connectivity_C5_eq

  Verification (spec §2A): AXLE independent — @ lean-4.32.0;
  `#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.Spectral
import Brockian.Connectivity
import Brockian.CycleSpectrumFamily
import Brockian.Geometry
import Brockian.Core

namespace Brockian.GoldenUniqueness

open Brockian.Spectral
open Brockian.Connectivity
open Brockian.CycleSpectrumFamily
open Brockian.Core
open Real

/-! ### Layer A — algebraic identities (no primality)

These are pure real-analytic / quadratic facts. They do not mention primes or
cycle spectra. They are the algebraic substrate that Layer B and Layer C use. -/

/-- **Algebraic bridge.**  `φ − 1 = 2 cos(2π/5)`.
Restatement of `Brockian.Spectral.golden_sub_one_eq_two_cos`. -/
theorem golden_sub_one_eq_two_cos :
    Real.goldenRatio - 1 = 2 * Real.cos (2 * Real.pi / 5) :=
  Brockian.Spectral.golden_sub_one_eq_two_cos

/-- **Golden reciprocal.**  `1/φ = φ − 1`.
Restatement of `Brockian.Connectivity.one_div_phi`. -/
theorem inv_golden_eq_sub_one :
    1 / Real.goldenRatio = Real.goldenRatio - 1 :=
  Brockian.Connectivity.one_div_phi

/-- **Companion angle.**  `2 cos(4π/5) = −φ`.
Restatement of `Brockian.Spectral.two_cos_four_pi_div_five`. -/
theorem two_cos_four_pi_div_five_eq_neg_golden :
    2 * Real.cos (4 * Real.pi / 5) = -Real.goldenRatio :=
  Brockian.Spectral.two_cos_four_pi_div_five

/-- **Three-way algebraic link.**  The golden shift, the reciprocal, and the
fundamental pentagon cosine are the same real number. Pure algebra — no spectrum. -/
theorem golden_algebraic_identity :
    Real.goldenRatio - 1 = 2 * Real.cos (2 * Real.pi / 5) ∧
    1 / Real.goldenRatio = Real.goldenRatio - 1 :=
  ⟨golden_sub_one_eq_two_cos, inv_golden_eq_sub_one⟩

/-- Core-φ form of the same cosine identity (uses `Brockian.Core.phi = Real.goldenRatio`
via the defining expansion). -/
theorem cos_two_pi_div_five_eq_phi_sub_one_div_two :
    Real.cos (2 * Real.pi / 5) = (phi - 1) / 2 :=
  Brockian.Core.cos_2pi_5

/-! ### Layer B — C₅ specialization (membership)

Pin φ − 1 and −φ as concrete adjacency eigenvalues of the 5-cycle. These are
witnesses, not uniqueness claims. -/

/-- **`φ − 1 ∈ cycleSpectrum 5`.** Witness k = 1. -/
theorem golden_mem_C5 :
    (Real.goldenRatio - 1) ∈ cycleSpectrum 5 :=
  Brockian.Spectral.golden_in_cycleSpectrum_five

/-- **`−φ ∈ cycleSpectrum 5`.** Witness k = 2. -/
theorem neg_golden_mem_C5 :
    (-Real.goldenRatio) ∈ cycleSpectrum 5 :=
  Brockian.Spectral.neg_golden_in_C5_spectrum

/-- **Fundamental C₅ mode equals the golden shift.**
`2 cos(2π/5) = φ − 1` (same as Layer A, oriented for spectrum use). -/
theorem two_cos_fundamental_mode_C5 :
    2 * Real.cos (2 * Real.pi / 5) = Real.goldenRatio - 1 :=
  golden_sub_one_eq_two_cos.symm

/-- CycleSpectrumFamily packaging: φ − 1 is the k = 1 mode of C₅. -/
theorem golden_in_C5_family :
    (Real.goldenRatio - 1) ∈ cycleSpectrum 5 :=
  Brockian.CycleSpectrumFamily.golden_in_C5

/-- Geometry packaging: the companion eigenvalue is −φ. -/
theorem golden_ratio_in_C5_geometry :
    2 * Real.cos (4 * Real.pi / 5) = -Real.goldenRatio := by
  -- Geometry uses Core.phi; align with Mathlib's goldenRatio.
  have hφ : phi = Real.goldenRatio := by
    unfold phi Real.goldenRatio; ring
  simpa [hφ] using Brockian.Geometry.golden_ratio_in_C5_spectrum

/-! ### Layer C — prime rigidity (the flagship schema)

Exactly `golden_unique_to_five`: among prime cycle lengths, φ − 1 appears in the
adjacency spectrum if and only if the length is 5. No stronger claim. -/

/-- **`golden_unique_to_five` (schema restatement).**
For any prime `p`,
  `(φ − 1) ∈ cycleSpectrum p  ↔  p = 5`.

`←` is the C₅ membership witness (Layer B). `→` is the cosine-equality +
`5 ∣ p` argument in `Brockian.Spectral`. This is the full content of the schema. -/
theorem golden_unique_to_five {p : ℕ} (hp : p.Prime) :
    (Real.goldenRatio - 1) ∈ cycleSpectrum p ↔ p = 5 :=
  Brockian.Spectral.golden_unique_to_five hp

/-- **Among primes, uniqueness of the golden cycle spectrum value.**
Alias with a name that stresses the prime-cycle scope (no claim about composite n). -/
theorem golden_unique_among_prime_cycles {p : ℕ} (hp : p.Prime) :
    (Real.goldenRatio - 1) ∈ cycleSpectrum p ↔ p = 5 :=
  golden_unique_to_five hp

/-- **Corollary: for a prime p ≠ 5, φ − 1 is not an adjacency eigenvalue of C_p.**
Direct one-direction unpacking of the flagship iff — nothing beyond it. -/
theorem golden_not_in_prime_cycle_ne_five {p : ℕ} (hp : p.Prime) (hne : p ≠ 5) :
    (Real.goldenRatio - 1) ∉ cycleSpectrum p := by
  intro hmem
  exact hne ((golden_unique_to_five hp).mp hmem)

/-- **Forward direction only.**  If φ − 1 is a C_p eigenvalue and p is prime, then p = 5. -/
theorem prime_cycle_golden_forces_five {p : ℕ} (hp : p.Prime)
    (hmem : (Real.goldenRatio - 1) ∈ cycleSpectrum p) : p = 5 :=
  (golden_unique_to_five hp).mp hmem

/-- **Backward direction only.**  On the prime 5, φ − 1 is present. -/
theorem five_carries_golden :
    (Real.goldenRatio - 1) ∈ cycleSpectrum 5 :=
  golden_mem_C5

/-! ### Separation summary (algebraic vs rigidity)

Named packaging so downstream code can import either layer without the other
claim. Algebraic identities never imply prime rigidity by themselves; rigidity
needs the circulant cosine comparison on a prime modulus. -/

/-- Bundle of pure algebraic equalities (Layer A). -/
theorem algebraic_layer :
    Real.goldenRatio - 1 = 2 * Real.cos (2 * Real.pi / 5) ∧
    1 / Real.goldenRatio = Real.goldenRatio - 1 ∧
    2 * Real.cos (4 * Real.pi / 5) = -Real.goldenRatio :=
  ⟨golden_sub_one_eq_two_cos, inv_golden_eq_sub_one, two_cos_four_pi_div_five_eq_neg_golden⟩

/-- Bundle of C₅ membership facts (Layer B). -/
theorem C5_membership_layer :
    (Real.goldenRatio - 1) ∈ cycleSpectrum 5 ∧
    (-Real.goldenRatio) ∈ cycleSpectrum 5 :=
  ⟨golden_mem_C5, neg_golden_mem_C5⟩

/-- Bundle of the prime-rigidity statement (Layer C) as a Prop-valued template. -/
theorem prime_rigidity_layer {p : ℕ} (hp : p.Prime) :
    (Real.goldenRatio - 1) ∈ cycleSpectrum p ↔ p = 5 :=
  golden_unique_to_five hp

/-! ### Optional Laplacian bridge (C₅ algebraic connectivity)

Connects the algebraic identity to the Connectivity / CycleSpectrumFamily
Laplacian packaging. Still no claim beyond C₅ / φ identities already proved. -/

/-- **C₅ algebraic connectivity equals `2 − 1/φ`.**
Restatement of `Connectivity.lambda2_eq` / `CycleSpectrumFamily.algebraic_connectivity_five`. -/
theorem algebraic_connectivity_C5_eq :
    2 - 2 * Real.cos (2 * Real.pi / 5) = 2 - 1 / Real.goldenRatio :=
  Brockian.CycleSpectrumFamily.algebraic_connectivity_five

/-- Algebraic connectivity membership + positivity + ordering for C₅. -/
theorem algebraic_connectivity_C5_props :
    (2 - 1 / Real.goldenRatio) ∈ Brockian.Connectivity.laplacianEigs5 ∧
    0 < 2 - 1 / Real.goldenRatio ∧
    (2 - 1 / Real.goldenRatio) ≤ 2 - 2 * Real.cos (4 * Real.pi / 5) :=
  Brockian.CycleSpectrumFamily.algebraic_connectivity_five_props

end Brockian.GoldenUniqueness
