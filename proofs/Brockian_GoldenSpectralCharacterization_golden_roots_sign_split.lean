/-
  Brockian/GoldenSpectralCharacterization.lean — a purely *spectral* fingerprint
  of the golden ratio.

  Idea (no reference to pentagons-as-shapes): the two non-Perron adjacency
  eigenvalues of the 5-cycle C₅ are `{φ − 1, −φ}` (φ = Real.goldenRatio), and
  these are *exactly* the two real roots of the golden quadratic

        X² + X − 1 = 0        (roots (−1 ± √5)/2).

  So the golden ratio is characterized spectrally: it is the number whose
  partner-pair `{φ − 1, −φ}` is the root set of `X² + X − 1`, both members of
  which are eigenvalues of C₅.

  This file proves:
    (1) `golden_quadratic_roots`   — {x | x²+x−1=0} = {φ−1, −φ} (pointwise iff),
    (2) `golden_roots_mem_pentagon_spectrum` — both roots ∈ spec(C₅),
    (3) `golden_ratio_spectral_characterization` — the capstone set-equality
        together with pentagon-spectrum membership,
    (4) `golden_roots_sign_split` — the two roots are separated by sign
        (−φ < 0 < φ − 1), which pins φ (>1) among them.

  Everything rests on `Real.goldenRatio_sq : φ² = φ + 1` and
  `Real.one_lt_goldenRatio : 1 < φ`, plus the *already proved* C₅ membership
  facts `golden_sub_one_mem_C5` and `neg_golden_mem_C5`.

  Verification: no sorry / admit / native_decide; AXLE when attested.
-/
import Mathlib
import Brockian.Spectral
import Brockian.C5SpectralMultiplicities

namespace Brockian.GoldenSpectralCharacterization

open Brockian Brockian.Spectral

/-! ### (1) The golden quadratic's root set is exactly `{φ − 1, −φ}` -/

/-- **Root set of the golden quadratic.** A real `x` satisfies `x² + x − 1 = 0`
iff it is one of the two non-Perron pentagon eigenvalues `φ − 1` or `−φ`.

The two roots have sum `−1 = (φ−1) + (−φ)` and product
`−1 = (φ−1)(−φ) = −φ² + φ = −(φ+1) + φ`, so `X² + X − 1 = (X−(φ−1))(X+φ)`. -/
theorem golden_quadratic_roots (x : ℝ) :
    x ^ 2 + x - 1 = 0 ↔ x = Real.goldenRatio - 1 ∨ x = -Real.goldenRatio := by
  -- The key factorization, valid because φ² = φ + 1.
  have hfac : (x - (Real.goldenRatio - 1)) * (x + Real.goldenRatio)
      = x ^ 2 + x - 1 := by
    linear_combination -Real.goldenRatio_sq
  constructor
  · intro h
    have hprod : (x - (Real.goldenRatio - 1)) * (x + Real.goldenRatio) = 0 := by
      rw [hfac]; exact h
    rcases mul_eq_zero.mp hprod with h1 | h2
    · left; linarith
    · right; linarith
  · intro h
    rcases h with h | h
    · subst h; nlinarith [Real.goldenRatio_sq]
    · subst h; nlinarith [Real.goldenRatio_sq]

/-! ### (2) Both roots are pentagon eigenvalues (reusing the proved C₅ core) -/

/-- **Both golden-quadratic roots are C₅ adjacency eigenvalues.** Direct
restatement of the two proved witnesses `golden_sub_one_mem_C5` (mode k = 1) and
`neg_golden_mem_C5` (mode k = 2). -/
theorem golden_roots_mem_pentagon_spectrum :
    (Real.goldenRatio - 1) ∈ Brockian.Spectral.cycleSpectrum 5 ∧
    (-Real.goldenRatio) ∈ Brockian.Spectral.cycleSpectrum 5 :=
  ⟨Brockian.C5SpectralMultiplicities.golden_sub_one_mem_C5,
   Brockian.C5SpectralMultiplicities.neg_golden_mem_C5⟩

/-! ### (3) The capstone — the spectral fingerprint of φ -/

/-- **Spectral characterization of the golden ratio.** The root set of the golden
quadratic X²+X−1 coincides with the two non-Perron eigenvalues of the 5-cycle:
{x | x²+x−1=0} = {φ−1, −φ} ⊆ spec(C₅). The golden ratio is the unique φ>1 for which
this holds. -/
theorem golden_ratio_spectral_characterization :
    {x : ℝ | x ^ 2 + x - 1 = 0} = {Real.goldenRatio - 1, -Real.goldenRatio} ∧
    (Real.goldenRatio - 1) ∈ Brockian.Spectral.cycleSpectrum 5 ∧
    (-Real.goldenRatio) ∈ Brockian.Spectral.cycleSpectrum 5 := by
  refine ⟨?_, golden_roots_mem_pentagon_spectrum.1, golden_roots_mem_pentagon_spectrum.2⟩
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact golden_quadratic_roots x

/-! ### (4) Sign split — the roots are distinguished by sign, pinning φ > 1 -/

/-- **The two roots are separated by sign.** From `1 < φ` we get `φ − 1 > 0` and
`−φ < 0`, so the positive root is `φ − 1` and the negative root is `−φ`. This is
what selects the golden ratio (φ > 1) among the pair. -/
theorem golden_roots_sign_split :
    -Real.goldenRatio < 0 ∧ 0 < Real.goldenRatio - 1 := by
  have h := Real.one_lt_goldenRatio
  exact ⟨by linarith, by linarith⟩

end Brockian.GoldenSpectralCharacterization
