/-
  Brockian/CosTraceNormTwoHundredSeventyOne.lean — spectral generator at p = 271.

  [ℚ(2 cos 2π/271):ℚ] = 135 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormTwoHundredSeventyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_twoHundredSeventyOne : Nat.Prime 271 := by decide

theorem twoHundredSeventyOne_ne_two : (271 : ℕ) ≠ 2 := by decide

theorem degree_twoHundredSeventyOne : (minpoly ℚ (spectralGen 271)).natDegree = 135 :=
  real_subfield_degree prime_twoHundredSeventyOne twoHundredSeventyOne_ne_two

theorem isIntegral_spectralGen_twoHundredSeventyOne : IsIntegral ℤ (spectralGen 271) :=
  isIntegral_spectralGen prime_twoHundredSeventyOne

theorem isIntegral_spectralGen_twoHundredSeventyOne_Q : IsIntegral ℚ (spectralGen 271) :=
  isIntegral_spectralGen_ℚ prime_twoHundredSeventyOne

theorem isIntegral_and_degree_twoHundredSeventyOne :
    IsIntegral ℤ (spectralGen 271) ∧
      (minpoly ℚ (spectralGen 271)).natDegree = 135 :=
  ⟨isIntegral_spectralGen_twoHundredSeventyOne, degree_twoHundredSeventyOne⟩

theorem twoHundredSeventyOne_pack :
    IsIntegral ℤ (spectralGen 271) ∧
      (minpoly ℚ (spectralGen 271)).natDegree = 135 :=
  isIntegral_and_degree_twoHundredSeventyOne

end Brockian.CosTraceNormTwoHundredSeventyOne
