/-
  Brockian/CosTraceNormFourHundredNinetyNine.lean — spectral generator at p = 499.

  [ℚ(2 cos 2π/499):ℚ] = 249 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFourHundredNinetyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fourHundredNinetyNine : Nat.Prime 499 := by decide

theorem fourHundredNinetyNine_ne_two : (499 : ℕ) ≠ 2 := by decide

theorem degree_fourHundredNinetyNine : (minpoly ℚ (spectralGen 499)).natDegree = 249 :=
  real_subfield_degree prime_fourHundredNinetyNine fourHundredNinetyNine_ne_two

theorem isIntegral_spectralGen_fourHundredNinetyNine : IsIntegral ℤ (spectralGen 499) :=
  isIntegral_spectralGen prime_fourHundredNinetyNine

theorem isIntegral_spectralGen_fourHundredNinetyNine_Q : IsIntegral ℚ (spectralGen 499) :=
  isIntegral_spectralGen_ℚ prime_fourHundredNinetyNine

theorem isIntegral_and_degree_fourHundredNinetyNine :
    IsIntegral ℤ (spectralGen 499) ∧
      (minpoly ℚ (spectralGen 499)).natDegree = 249 :=
  ⟨isIntegral_spectralGen_fourHundredNinetyNine, degree_fourHundredNinetyNine⟩

theorem fourHundredNinetyNine_pack :
    IsIntegral ℤ (spectralGen 499) ∧
      (minpoly ℚ (spectralGen 499)).natDegree = 249 :=
  isIntegral_and_degree_fourHundredNinetyNine

end Brockian.CosTraceNormFourHundredNinetyNine
