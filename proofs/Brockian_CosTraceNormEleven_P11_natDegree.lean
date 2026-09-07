/-
  Brockian/CosTraceNormEleven.lean — spectral generator at `p = 11`, plus the
  solid odd-prime packaging that the `{3,5,7}` CosTraceNorm file left open.

  Extends `CosTraceNorm` / `CosAlgebraicInteger` / `GaloisWhyFive` style to the
  next prime after the cubic case.  The degree is forced by the general theorem
  of `GaloisGeneralDegree`:

        `[ℚ(2 cos(2π/11)) : ℚ] = (11 − 1)/2 = 5`.

  The explicit monic minpoly of degree 5 is the Chebyshev family `Ψ_11` of
  `GaloisMinPolyFamily`, expanded to the classical integer polynomial

        `P11 = X⁵ + X⁴ − 4X³ − 3X² + 3X + 1`.

  Trace / Norm then follow from monic minpoly coefficients (no numerology):

        Trace = −a₄ = −1,   Norm = (−1)⁵ a₀ = −1.

  ## What is proved

    * General odd-prime solid lemmas (re-exported / packaged):
        `isIntegral_spectralGen_odd`, `degree_odd_prime`,
        `isIntegral_and_degree_odd`, `minpoly_eq_Psi`,
        `trace_adjoin_gen_eq_neg_nextCoeff`, `norm_adjoin_gen_eq_coeff_zero`.
    * p = 11 degree pack: `degree_eleven`, `degree_eleven_pack`.
    * Integrality: `isIntegral_spectralGen_eleven`, `isIntegral_spectralGen_eleven_ℚ`.
    * Explicit minpoly: `P11`, `Psi_eleven`, `minpoly_eleven`.
    * Coefficient packs + Trace/Norm:
        nextCoeff = 1, coeff 0 = 1 → Trace = −1, Norm = −1.
    * Combined pack: `eleven_pack`, `trace_norm_eleven_pack`.

  ## What is NOT claimed

    * No inventing of a false minpoly: `P11` is identified with `Ψ_11` by the
      Chebyshev recurrence, and `Ψ_11 = minpoly` is already proved for all odd
      primes in `GaloisMinPolyFamily`.
    * p = 2 remains the degenerate boundary excluded by `GaloisGeneralDegree`.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.CosTraceNorm
import Brockian.GaloisGeneralDegree
import Brockian.GaloisMinPolyFamily
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormEleven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.GaloisMinPolyFamily
open Brockian.CosAlgebraicInteger
open Brockian.CosTraceNorm

/-! ### General odd-prime solid lemmas
(from GaloisGeneralDegree + CosAlgebraicInteger + GaloisMinPolyFamily + CosTraceNorm) -/

/-- **Integrality (odd primes).**  `α_p = 2 cos(2π/p)` is an algebraic integer. -/
theorem isIntegral_spectralGen_odd {p : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2) :
    IsIntegral ℤ (spectralGen p) :=
  CosAlgebraicInteger.isIntegral_spectralGen hp

/-- **Integrality over `ℚ` (odd primes).** -/
theorem isIntegral_spectralGen_odd_ℚ {p : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2) :
    IsIntegral ℚ (spectralGen p) :=
  CosAlgebraicInteger.isIntegral_spectralGen_ℚ hp

/-- **Degree (odd primes).**  `[ℚ(α_p):ℚ] = (p − 1)/2`. -/
theorem degree_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (minpoly ℚ (spectralGen p)).natDegree = (p - 1) / 2 :=
  real_subfield_degree hp hp2

/-- **Combined arithmetic face for every odd prime:** algebraic integer of degree
`(p − 1)/2`. -/
theorem isIntegral_and_degree_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    IsIntegral ℤ (spectralGen p) ∧
      (minpoly ℚ (spectralGen p)).natDegree = (p - 1) / 2 :=
  CosAlgebraicInteger.isIntegral_and_degree hp hp2

/-- **Minpoly family identification (odd primes).**  `minpoly ℚ α_p = Ψ_p`. -/
theorem minpoly_eq_Psi {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    minpoly ℚ (spectralGen p) = Psi p :=
  (Psi_eq_minpoly hp hp2).symm

/-- Re-export of the general Trace coefficient rule. -/
theorem trace_adjoin_gen_eq_neg_nextCoeff {x : ℝ} (hx : IsIntegral ℚ x) :
    Algebra.trace ℚ ℚ⟮x⟯ (AdjoinSimple.gen ℚ x) = -(minpoly ℚ x).nextCoeff :=
  CosTraceNorm.trace_adjoin_gen_eq_neg_nextCoeff hx

/-- Re-export of the general Norm coefficient rule. -/
theorem norm_adjoin_gen_eq_coeff_zero {x : ℝ} (hx : IsIntegral ℚ x) :
    Algebra.norm ℚ (AdjoinSimple.gen ℚ x) =
      (-1) ^ (minpoly ℚ x).natDegree * (minpoly ℚ x).coeff 0 :=
  CosTraceNorm.norm_adjoin_gen_eq_coeff_zero hx

/-! ### p = 11: degree and integrality -/

/-- `11` is prime (decidable). -/
theorem prime_eleven : Nat.Prime 11 := by decide

/-- `11 ≠ 2`. -/
theorem eleven_ne_two : (11 : ℕ) ≠ 2 := by decide

/-- **`[ℚ(α_11):ℚ] = 5`.**  From the general degree theorem: `(11 − 1)/2 = 5`
(definitionally). -/
theorem degree_eleven : (minpoly ℚ (spectralGen 11)).natDegree = 5 :=
  degree_odd_prime prime_eleven eleven_ne_two

/-- Degree pack alias matching the CosAlgebraicInteger `degree_*_pack` style. -/
theorem degree_eleven_pack : (minpoly ℚ (spectralGen 11)).natDegree = 5 :=
  degree_eleven

/-- `α_11` is an algebraic integer over `ℤ`. -/
theorem isIntegral_spectralGen_eleven : IsIntegral ℤ (spectralGen 11) :=
  isIntegral_spectralGen_odd prime_eleven eleven_ne_two

/-- `α_11` is integral over `ℚ`. -/
theorem isIntegral_spectralGen_eleven_ℚ : IsIntegral ℚ (spectralGen 11) :=
  isIntegral_spectralGen_odd_ℚ prime_eleven eleven_ne_two

/-- Combined integrality + degree for `p = 11`. -/
theorem isIntegral_and_degree_eleven :
    IsIntegral ℤ (spectralGen 11) ∧
      (minpoly ℚ (spectralGen 11)).natDegree = 5 :=
  ⟨isIntegral_spectralGen_eleven, degree_eleven⟩

/-! ### Explicit monic degree-5 annihilator `P11` -/

/-- **Classical monic integer polynomial for `α_11`:**
`X⁵ + X⁴ − 4X³ − 3X² + 3X + 1`.  Equal to the Chebyshev family `Ψ_11`. -/
noncomputable def P11 : Polynomial ℚ :=
  X ^ 5 + X ^ 4 - 4 * X ^ 3 - 3 * X ^ 2 + 3 * X + 1

theorem P11_monic : P11.Monic := by unfold P11; monicity!

theorem P11_natDegree : P11.natDegree = 5 := by unfold P11; compute_degree!

/-! ### Chebyshev expansion: `Ψ_11 = P11` -/

/-- `C ℚ 3 = X³ − 3X`. -/
private theorem C_three : Chebyshev.C ℚ (3 : ℤ) = X ^ 3 - 3 * X := by
  have h := Chebyshev.C_add_two ℚ (1 : ℤ)
  rw [show (1 : ℤ) + 2 = 3 from by norm_num, show (1 : ℤ) + 1 = 2 from by norm_num,
    Chebyshev.C_two, Chebyshev.C_one] at h
  rw [h]; ring

/-- `C ℚ 4 = X⁴ − 4X² + 2`. -/
private theorem C_four : Chebyshev.C ℚ (4 : ℤ) = X ^ 4 - 4 * X ^ 2 + 2 := by
  have h := Chebyshev.C_add_two ℚ (2 : ℤ)
  rw [show (2 : ℤ) + 2 = 4 from by norm_num, show (2 : ℤ) + 1 = 3 from by norm_num,
    Chebyshev.C_two, C_three] at h
  rw [h]; ring

/-- `C ℚ 5 = X⁵ − 5X³ + 5X`. -/
private theorem C_five : Chebyshev.C ℚ (5 : ℤ) = X ^ 5 - 5 * X ^ 3 + 5 * X := by
  have h := Chebyshev.C_add_two ℚ (3 : ℤ)
  rw [show (3 : ℤ) + 2 = 5 from by norm_num, show (3 : ℤ) + 1 = 4 from by norm_num,
    C_three, C_four] at h
  rw [h]; ring

/-- **`Ψ_11 = P11`.**  Expand the Chebyshev sum of degree 5 and reduce by ring. -/
theorem Psi_eleven : Psi 11 = P11 := by
  unfold Psi P11
  rw [show (11 - 1) / 2 = ((((0 + 1) + 1) + 1) + 1) + 1 from by norm_num,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    show ((((((0 + 1) + 1) + 1) + 1) + 1 : ℕ) : ℤ) = 5 from by norm_num,
    show (((((0 + 1) + 1) + 1) + 1 : ℕ) : ℤ) = 4 from by norm_num,
    show ((((0 + 1) + 1) + 1 : ℕ) : ℤ) = 3 from by norm_num,
    show (((0 + 1) + 1 : ℕ) : ℤ) = 2 from by norm_num,
    show ((0 + 1 : ℕ) : ℤ) = 1 from by norm_num,
    Chebyshev.C_one, Chebyshev.C_two, C_three, C_four, C_five]
  ring

/-- **`minpoly ℚ α_11 = P11`.**  Family identification + Chebyshev expansion. -/
theorem minpoly_eleven : minpoly ℚ (spectralGen 11) = P11 := by
  rw [minpoly_eq_Psi prime_eleven eleven_ne_two, Psi_eleven]

/-! ### Coefficient packs for p = 11 -/

theorem nextCoeff_minpoly_eleven : (minpoly ℚ (spectralGen 11)).nextCoeff = 1 := by
  rw [minpoly_eleven, nextCoeff_of_natDegree_pos (by rw [P11_natDegree]; norm_num),
    P11_natDegree]
  unfold P11
  simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_one]

theorem coeff_zero_minpoly_eleven : (minpoly ℚ (spectralGen 11)).coeff 0 = 1 := by
  rw [minpoly_eleven]
  unfold P11
  simp [coeff_add, coeff_sub, coeff_X_pow, coeff_X, coeff_one]

/-! ### Trace / Norm for p = 11 -/

/-- **p = 11:** `Trace_{ℚ(α_11)/ℚ}(α_11) = −1` (from `a_4 = 1` in `P11`). -/
theorem trace_spectralGen_eleven :
    Algebra.trace ℚ ℚ⟮spectralGen 11⟯ (AdjoinSimple.gen ℚ (spectralGen 11)) = -1 := by
  rw [trace_adjoin_gen_eq_neg_nextCoeff isIntegral_spectralGen_eleven_ℚ,
    nextCoeff_minpoly_eleven]

/-- **p = 11:** `Norm_{ℚ(α_11)/ℚ}(α_11) = −1` (from `(−1)⁵ · 1`). -/
theorem norm_spectralGen_eleven :
    Algebra.norm ℚ (AdjoinSimple.gen ℚ (spectralGen 11)) = -1 := by
  rw [norm_adjoin_gen_eq_coeff_zero isIntegral_spectralGen_eleven_ℚ,
    degree_eleven, coeff_zero_minpoly_eleven]
  norm_num

/-- Combined Trace + Norm pack for `p = 11`. -/
theorem trace_norm_eleven_pack :
    Algebra.trace ℚ ℚ⟮spectralGen 11⟯ (AdjoinSimple.gen ℚ (spectralGen 11)) = -1 ∧
      Algebra.norm ℚ (AdjoinSimple.gen ℚ (spectralGen 11)) = -1 :=
  ⟨trace_spectralGen_eleven, norm_spectralGen_eleven⟩

/-- Full p = 11 package: integrality, degree 5, minpoly, Trace = −1, Norm = −1. -/
theorem eleven_pack :
    IsIntegral ℤ (spectralGen 11) ∧
      (minpoly ℚ (spectralGen 11)).natDegree = 5 ∧
      minpoly ℚ (spectralGen 11) = P11 ∧
      Algebra.trace ℚ ℚ⟮spectralGen 11⟯ (AdjoinSimple.gen ℚ (spectralGen 11)) = -1 ∧
      Algebra.norm ℚ (AdjoinSimple.gen ℚ (spectralGen 11)) = -1 :=
  ⟨isIntegral_spectralGen_eleven, degree_eleven, minpoly_eleven,
    trace_spectralGen_eleven, norm_spectralGen_eleven⟩

end Brockian.CosTraceNormEleven
