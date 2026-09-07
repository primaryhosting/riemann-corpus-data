/-
  Brockian/CosTraceNormFourHundredTwentyOne.lean — spectral generator at p = 421.

  [ℚ(2 cos 2π/421):ℚ] = 210 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFourHundredTwentyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fourHundredTwentyOne : Nat.Prime 421 := by decide

theorem fourHundredTwentyOne_ne_two : (421 : ℕ) ≠ 2 := by decide

theorem degree_fourHundredTwentyOne : (minpoly ℚ (spectralGen 421)).natDegree = 210 :=
  real_subfield_degree prime_fourHundredTwentyOne fourHundredTwentyOne_ne_two

theorem isIntegral_spectralGen_fourHundredTwentyOne : IsIntegral ℤ (spectralGen 421) :=
  isIntegral_spectralGen prime_fourHundredTwentyOne

theorem isIntegral_spectralGen_fourHundredTwentyOne_Q : IsIntegral ℚ (spectralGen 421) :=
  isIntegral_spectralGen_ℚ prime_fourHundredTwentyOne

theorem isIntegral_and_degree_fourHundredTwentyOne :
    IsIntegral ℤ (spectralGen 421) ∧
      (minpoly ℚ (spectralGen 421)).natDegree = 210 :=
  ⟨isIntegral_spectralGen_fourHundredTwentyOne, degree_fourHundredTwentyOne⟩

theorem fourHundredTwentyOne_pack :
    IsIntegral ℤ (spectralGen 421) ∧
      (minpoly ℚ (spectralGen 421)).natDegree = 210 :=
  isIntegral_and_degree_fourHundredTwentyOne

end Brockian.CosTraceNormFourHundredTwentyOne
