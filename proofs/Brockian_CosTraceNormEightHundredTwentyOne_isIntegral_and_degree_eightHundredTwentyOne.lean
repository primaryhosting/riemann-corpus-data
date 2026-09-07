/-
  Brockian/CosTraceNormEightHundredTwentyOne.lean — spectral generator at p = 821.

  [ℚ(2 cos 2π/821):ℚ] = 410 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormEightHundredTwentyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_eightHundredTwentyOne : Nat.Prime 821 := by decide

theorem eightHundredTwentyOne_ne_two : (821 : ℕ) ≠ 2 := by decide

theorem degree_eightHundredTwentyOne : (minpoly ℚ (spectralGen 821)).natDegree = 410 :=
  real_subfield_degree prime_eightHundredTwentyOne eightHundredTwentyOne_ne_two

theorem isIntegral_spectralGen_eightHundredTwentyOne : IsIntegral ℤ (spectralGen 821) :=
  isIntegral_spectralGen prime_eightHundredTwentyOne

theorem isIntegral_spectralGen_eightHundredTwentyOne_Q : IsIntegral ℚ (spectralGen 821) :=
  isIntegral_spectralGen_ℚ prime_eightHundredTwentyOne

theorem isIntegral_and_degree_eightHundredTwentyOne :
    IsIntegral ℤ (spectralGen 821) ∧
      (minpoly ℚ (spectralGen 821)).natDegree = 410 :=
  ⟨isIntegral_spectralGen_eightHundredTwentyOne, degree_eightHundredTwentyOne⟩

theorem eightHundredTwentyOne_pack :
    IsIntegral ℤ (spectralGen 821) ∧
      (minpoly ℚ (spectralGen 821)).natDegree = 410 :=
  isIntegral_and_degree_eightHundredTwentyOne

end Brockian.CosTraceNormEightHundredTwentyOne
