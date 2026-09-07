/-
  Brockian/CosTraceNormTwoHundredSixtyNine.lean — spectral generator at p = 269.

  [ℚ(2 cos 2π/269):ℚ] = 134 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormTwoHundredSixtyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_twoHundredSixtyNine : Nat.Prime 269 := by decide

theorem twoHundredSixtyNine_ne_two : (269 : ℕ) ≠ 2 := by decide

theorem degree_twoHundredSixtyNine : (minpoly ℚ (spectralGen 269)).natDegree = 134 :=
  real_subfield_degree prime_twoHundredSixtyNine twoHundredSixtyNine_ne_two

theorem isIntegral_spectralGen_twoHundredSixtyNine : IsIntegral ℤ (spectralGen 269) :=
  isIntegral_spectralGen prime_twoHundredSixtyNine

theorem isIntegral_spectralGen_twoHundredSixtyNine_Q : IsIntegral ℚ (spectralGen 269) :=
  isIntegral_spectralGen_ℚ prime_twoHundredSixtyNine

theorem isIntegral_and_degree_twoHundredSixtyNine :
    IsIntegral ℤ (spectralGen 269) ∧
      (minpoly ℚ (spectralGen 269)).natDegree = 134 :=
  ⟨isIntegral_spectralGen_twoHundredSixtyNine, degree_twoHundredSixtyNine⟩

theorem twoHundredSixtyNine_pack :
    IsIntegral ℤ (spectralGen 269) ∧
      (minpoly ℚ (spectralGen 269)).natDegree = 134 :=
  isIntegral_and_degree_twoHundredSixtyNine

end Brockian.CosTraceNormTwoHundredSixtyNine
