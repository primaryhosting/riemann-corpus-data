/-
  Brockian/CosTraceNormFiveHundredSeventyOne.lean — spectral generator at p = 571.

  [ℚ(2 cos 2π/571):ℚ] = 285 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFiveHundredSeventyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fiveHundredSeventyOne : Nat.Prime 571 := by decide

theorem fiveHundredSeventyOne_ne_two : (571 : ℕ) ≠ 2 := by decide

theorem degree_fiveHundredSeventyOne : (minpoly ℚ (spectralGen 571)).natDegree = 285 :=
  real_subfield_degree prime_fiveHundredSeventyOne fiveHundredSeventyOne_ne_two

theorem isIntegral_spectralGen_fiveHundredSeventyOne : IsIntegral ℤ (spectralGen 571) :=
  isIntegral_spectralGen prime_fiveHundredSeventyOne

theorem isIntegral_spectralGen_fiveHundredSeventyOne_Q : IsIntegral ℚ (spectralGen 571) :=
  isIntegral_spectralGen_ℚ prime_fiveHundredSeventyOne

theorem isIntegral_and_degree_fiveHundredSeventyOne :
    IsIntegral ℤ (spectralGen 571) ∧
      (minpoly ℚ (spectralGen 571)).natDegree = 285 :=
  ⟨isIntegral_spectralGen_fiveHundredSeventyOne, degree_fiveHundredSeventyOne⟩

theorem fiveHundredSeventyOne_pack :
    IsIntegral ℤ (spectralGen 571) ∧
      (minpoly ℚ (spectralGen 571)).natDegree = 285 :=
  isIntegral_and_degree_fiveHundredSeventyOne

end Brockian.CosTraceNormFiveHundredSeventyOne
