/-
  Brockian/NewEra.lean — the verified reading path (gallery module).

  Collects flagship theorems under one namespace. No new deep mathematics:
  re-exports only. Does not claim RH, Goldbach, or ESA of −Δ+V.

  Charter: docs/NEW-ERA.md · Gallery: observatory/era.html
-/
import Mathlib
import Brockian.Spectral
import Brockian.Admissibility
import Brockian.WeylOperatorChoice
import Brockian.WeylConfining
import Brockian.SpectralGate1

open MeasureTheory Complex
open Brockian.Spectral
open Brockian.Admissibility
open Brockian.Weyl.OperatorChoice
open Brockian.Weyl.Confining
open Brockian.SpectralGate1

namespace Brockian.NewEra

/-! ### Why five -/

/-- **Flagship.** For prime `p`, `φ − 1 ∈ spec(C_p)` iff `p = 5`. -/
theorem why_five {p : ℕ} (hp : p.Prime) :
    (Real.goldenRatio - 1 ∈ cycleSpectrum p) ↔ p = 5 :=
  golden_unique_to_five hp

/-- Algebraic fingerprint of the pentagon angle. -/
theorem pentagon_cosine_is_golden :
    Real.goldenRatio - 1 = 2 * Real.cos (2 * Real.pi / 5) :=
  golden_sub_one_eq_two_cos

/-- Membership: the golden shift is a C₅ eigenvalue. -/
theorem golden_lives_on_the_pentagon :
    Real.goldenRatio - 1 ∈ cycleSpectrum 5 :=
  golden_in_cycleSpectrum_five

/-- Membership: the companion −φ is a C₅ eigenvalue. -/
theorem neg_golden_lives_on_the_pentagon :
    -Real.goldenRatio ∈ cycleSpectrum 5 :=
  Brockian.Spectral.neg_golden_in_C5_spectrum

/-! ### Selection laws -/

/-- Twin constraint: one admissible start mod 3. -/
theorem twin_admissible_count (g : ZMod 3) (hg : g ≠ 0) :
    (admissibleResidues 3 g).card = 1 :=
  admissibility_count_three g hg

/-- Brockian case: three admissible starts mod 5. -/
theorem brockian_admissible_count (g : ZMod 5) (hg : g ≠ 0) :
    (admissibleResidues 5 g).card = 3 :=
  admissibility_count_five g hg

/-! ### Gate 1 honesty -/

/-- Decaying prime-Gaussian cannot realize large Hilbert–Pólya eigenvalues. -/
theorem decaying_potential_cannot_realize_large_zeros {s : ℂ}
    (hz : riemannZeta s = 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (hs1 : s ≠ 1)
    (hball : (2 : ℝ) < ‖s - 1 / 2‖)
    (v : Lp ℂ 2 (volume : Measure ℝ)) (hv : v ≠ 0) :
    primeGaussianMulCLM v ≠ (-I * (s - 1 / 2)) • v :=
  primeGaussian_not_realize_large_zero hz htriv hs1 hball v hv

/-- Quadratic growth is confining (shape only). -/
theorem quadratic_is_confining : IsConfining fun x : ℝ => x ^ 2 :=
  quadratic_isConfining

/-- Gate-1 prime-Gaussian is not confining. -/
theorem primeGaussian_not_confining : ¬ IsConfining primeGaussian :=
  primeGaussian_not_isConfining

/-! ### Reading path package -/

/-- Flagship package: rigidity + shape honesty. RH is not included. -/
structure ReadingPath where
  why_five : ∀ {p : ℕ}, p.Prime →
    ((Real.goldenRatio - 1 ∈ cycleSpectrum p) ↔ p = 5)
  golden_on_C5 : Real.goldenRatio - 1 ∈ cycleSpectrum 5
  shape : ¬ IsConfining primeGaussian

noncomputable def readingPath : ReadingPath where
  why_five := fun {_} hp => why_five hp
  golden_on_C5 := golden_lives_on_the_pentagon
  shape := primeGaussian_not_confining

end Brockian.NewEra
