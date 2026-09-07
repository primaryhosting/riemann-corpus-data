/-
  Brockian/CosTraceNormFiveHundredTwentyOne.lean — spectral generator at p = 521.

  [ℚ(2 cos 2π/521):ℚ] = 260 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFiveHundredTwentyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fiveHundredTwentyOne : Nat.Prime 521 := by decide

theorem fiveHundredTwentyOne_ne_two : (521 : ℕ) ≠ 2 := by decide

theorem degree_fiveHundredTwentyOne : (minpoly ℚ (spectralGen 521)).natDegree = 260 :=
  real_subfield_degree prime_fiveHundredTwentyOne fiveHundredTwentyOne_ne_two

theorem isIntegral_spectralGen_fiveHundredTwentyOne : IsIntegral ℤ (spectralGen 521) :=
  isIntegral_spectralGen prime_fiveHundredTwentyOne

theorem isIntegral_spectralGen_fiveHundredTwentyOne_Q : IsIntegral ℚ (spectralGen 521) :=
  isIntegral_spectralGen_ℚ prime_fiveHundredTwentyOne

theorem isIntegral_and_degree_fiveHundredTwentyOne :
    IsIntegral ℤ (spectralGen 521) ∧
      (minpoly ℚ (spectralGen 521)).natDegree = 260 :=
  ⟨isIntegral_spectralGen_fiveHundredTwentyOne, degree_fiveHundredTwentyOne⟩

theorem fiveHundredTwentyOne_pack :
    IsIntegral ℤ (spectralGen 521) ∧
      (minpoly ℚ (spectralGen 521)).natDegree = 260 :=
  isIntegral_and_degree_fiveHundredTwentyOne

end Brockian.CosTraceNormFiveHundredTwentyOne
