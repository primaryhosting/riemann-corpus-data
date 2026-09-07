/-
  Brockian/CosTraceNormFourHundredSixtyOne.lean — spectral generator at p = 461.

  [ℚ(2 cos 2π/461):ℚ] = 230 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFourHundredSixtyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fourHundredSixtyOne : Nat.Prime 461 := by decide

theorem fourHundredSixtyOne_ne_two : (461 : ℕ) ≠ 2 := by decide

theorem degree_fourHundredSixtyOne : (minpoly ℚ (spectralGen 461)).natDegree = 230 :=
  real_subfield_degree prime_fourHundredSixtyOne fourHundredSixtyOne_ne_two

theorem isIntegral_spectralGen_fourHundredSixtyOne : IsIntegral ℤ (spectralGen 461) :=
  isIntegral_spectralGen prime_fourHundredSixtyOne

theorem isIntegral_spectralGen_fourHundredSixtyOne_Q : IsIntegral ℚ (spectralGen 461) :=
  isIntegral_spectralGen_ℚ prime_fourHundredSixtyOne

theorem isIntegral_and_degree_fourHundredSixtyOne :
    IsIntegral ℤ (spectralGen 461) ∧
      (minpoly ℚ (spectralGen 461)).natDegree = 230 :=
  ⟨isIntegral_spectralGen_fourHundredSixtyOne, degree_fourHundredSixtyOne⟩

theorem fourHundredSixtyOne_pack :
    IsIntegral ℤ (spectralGen 461) ∧
      (minpoly ℚ (spectralGen 461)).natDegree = 230 :=
  isIntegral_and_degree_fourHundredSixtyOne

end Brockian.CosTraceNormFourHundredSixtyOne
