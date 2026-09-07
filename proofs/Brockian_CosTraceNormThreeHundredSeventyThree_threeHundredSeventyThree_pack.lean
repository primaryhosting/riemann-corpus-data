/-
  Brockian/CosTraceNormThreeHundredSeventyThree.lean — spectral generator at p = 373.

  [ℚ(2 cos 2π/373):ℚ] = 186 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormThreeHundredSeventyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_threeHundredSeventyThree : Nat.Prime 373 := by decide

theorem threeHundredSeventyThree_ne_two : (373 : ℕ) ≠ 2 := by decide

theorem degree_threeHundredSeventyThree : (minpoly ℚ (spectralGen 373)).natDegree = 186 :=
  real_subfield_degree prime_threeHundredSeventyThree threeHundredSeventyThree_ne_two

theorem isIntegral_spectralGen_threeHundredSeventyThree : IsIntegral ℤ (spectralGen 373) :=
  isIntegral_spectralGen prime_threeHundredSeventyThree

theorem isIntegral_spectralGen_threeHundredSeventyThree_Q : IsIntegral ℚ (spectralGen 373) :=
  isIntegral_spectralGen_ℚ prime_threeHundredSeventyThree

theorem isIntegral_and_degree_threeHundredSeventyThree :
    IsIntegral ℤ (spectralGen 373) ∧
      (minpoly ℚ (spectralGen 373)).natDegree = 186 :=
  ⟨isIntegral_spectralGen_threeHundredSeventyThree, degree_threeHundredSeventyThree⟩

theorem threeHundredSeventyThree_pack :
    IsIntegral ℤ (spectralGen 373) ∧
      (minpoly ℚ (spectralGen 373)).natDegree = 186 :=
  isIntegral_and_degree_threeHundredSeventyThree

end Brockian.CosTraceNormThreeHundredSeventyThree
