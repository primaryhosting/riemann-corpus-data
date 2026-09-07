/-
  Brockian/CosTraceNormSixHundredSixtyOne.lean — spectral generator at p = 661.

  [ℚ(2 cos 2π/661):ℚ] = 330 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSixHundredSixtyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sixHundredSixtyOne : Nat.Prime 661 := by decide

theorem sixHundredSixtyOne_ne_two : (661 : ℕ) ≠ 2 := by decide

theorem degree_sixHundredSixtyOne : (minpoly ℚ (spectralGen 661)).natDegree = 330 :=
  real_subfield_degree prime_sixHundredSixtyOne sixHundredSixtyOne_ne_two

theorem isIntegral_spectralGen_sixHundredSixtyOne : IsIntegral ℤ (spectralGen 661) :=
  isIntegral_spectralGen prime_sixHundredSixtyOne

theorem isIntegral_spectralGen_sixHundredSixtyOne_Q : IsIntegral ℚ (spectralGen 661) :=
  isIntegral_spectralGen_ℚ prime_sixHundredSixtyOne

theorem isIntegral_and_degree_sixHundredSixtyOne :
    IsIntegral ℤ (spectralGen 661) ∧
      (minpoly ℚ (spectralGen 661)).natDegree = 330 :=
  ⟨isIntegral_spectralGen_sixHundredSixtyOne, degree_sixHundredSixtyOne⟩

theorem sixHundredSixtyOne_pack :
    IsIntegral ℤ (spectralGen 661) ∧
      (minpoly ℚ (spectralGen 661)).natDegree = 330 :=
  isIntegral_and_degree_sixHundredSixtyOne

end Brockian.CosTraceNormSixHundredSixtyOne
