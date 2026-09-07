/-
  Brockian/CosTraceNormTwoHundredEightyOne.lean — spectral generator at p = 281.

  [ℚ(2 cos 2π/281):ℚ] = 140 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormTwoHundredEightyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_twoHundredEightyOne : Nat.Prime 281 := by decide

theorem twoHundredEightyOne_ne_two : (281 : ℕ) ≠ 2 := by decide

theorem degree_twoHundredEightyOne : (minpoly ℚ (spectralGen 281)).natDegree = 140 :=
  real_subfield_degree prime_twoHundredEightyOne twoHundredEightyOne_ne_two

theorem isIntegral_spectralGen_twoHundredEightyOne : IsIntegral ℤ (spectralGen 281) :=
  isIntegral_spectralGen prime_twoHundredEightyOne

theorem isIntegral_spectralGen_twoHundredEightyOne_Q : IsIntegral ℚ (spectralGen 281) :=
  isIntegral_spectralGen_ℚ prime_twoHundredEightyOne

theorem isIntegral_and_degree_twoHundredEightyOne :
    IsIntegral ℤ (spectralGen 281) ∧
      (minpoly ℚ (spectralGen 281)).natDegree = 140 :=
  ⟨isIntegral_spectralGen_twoHundredEightyOne, degree_twoHundredEightyOne⟩

theorem twoHundredEightyOne_pack :
    IsIntegral ℤ (spectralGen 281) ∧
      (minpoly ℚ (spectralGen 281)).natDegree = 140 :=
  isIntegral_and_degree_twoHundredEightyOne

end Brockian.CosTraceNormTwoHundredEightyOne
