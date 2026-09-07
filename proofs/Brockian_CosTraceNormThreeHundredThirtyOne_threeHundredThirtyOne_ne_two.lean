/-
  Brockian/CosTraceNormThreeHundredThirtyOne.lean — spectral generator at p = 331.

  [ℚ(2 cos 2π/331):ℚ] = 165 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormThreeHundredThirtyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_threeHundredThirtyOne : Nat.Prime 331 := by decide

theorem threeHundredThirtyOne_ne_two : (331 : ℕ) ≠ 2 := by decide

theorem degree_threeHundredThirtyOne : (minpoly ℚ (spectralGen 331)).natDegree = 165 :=
  real_subfield_degree prime_threeHundredThirtyOne threeHundredThirtyOne_ne_two

theorem isIntegral_spectralGen_threeHundredThirtyOne : IsIntegral ℤ (spectralGen 331) :=
  isIntegral_spectralGen prime_threeHundredThirtyOne

theorem isIntegral_spectralGen_threeHundredThirtyOne_Q : IsIntegral ℚ (spectralGen 331) :=
  isIntegral_spectralGen_ℚ prime_threeHundredThirtyOne

theorem isIntegral_and_degree_threeHundredThirtyOne :
    IsIntegral ℤ (spectralGen 331) ∧
      (minpoly ℚ (spectralGen 331)).natDegree = 165 :=
  ⟨isIntegral_spectralGen_threeHundredThirtyOne, degree_threeHundredThirtyOne⟩

theorem threeHundredThirtyOne_pack :
    IsIntegral ℤ (spectralGen 331) ∧
      (minpoly ℚ (spectralGen 331)).natDegree = 165 :=
  isIntegral_and_degree_threeHundredThirtyOne

end Brockian.CosTraceNormThreeHundredThirtyOne
