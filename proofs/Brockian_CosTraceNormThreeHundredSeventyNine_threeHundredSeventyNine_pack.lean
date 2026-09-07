/-
  Brockian/CosTraceNormThreeHundredSeventyNine.lean — spectral generator at p = 379.

  [ℚ(2 cos 2π/379):ℚ] = 189 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormThreeHundredSeventyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_threeHundredSeventyNine : Nat.Prime 379 := by decide

theorem threeHundredSeventyNine_ne_two : (379 : ℕ) ≠ 2 := by decide

theorem degree_threeHundredSeventyNine : (minpoly ℚ (spectralGen 379)).natDegree = 189 :=
  real_subfield_degree prime_threeHundredSeventyNine threeHundredSeventyNine_ne_two

theorem isIntegral_spectralGen_threeHundredSeventyNine : IsIntegral ℤ (spectralGen 379) :=
  isIntegral_spectralGen prime_threeHundredSeventyNine

theorem isIntegral_spectralGen_threeHundredSeventyNine_Q : IsIntegral ℚ (spectralGen 379) :=
  isIntegral_spectralGen_ℚ prime_threeHundredSeventyNine

theorem isIntegral_and_degree_threeHundredSeventyNine :
    IsIntegral ℤ (spectralGen 379) ∧
      (minpoly ℚ (spectralGen 379)).natDegree = 189 :=
  ⟨isIntegral_spectralGen_threeHundredSeventyNine, degree_threeHundredSeventyNine⟩

theorem threeHundredSeventyNine_pack :
    IsIntegral ℤ (spectralGen 379) ∧
      (minpoly ℚ (spectralGen 379)).natDegree = 189 :=
  isIntegral_and_degree_threeHundredSeventyNine

end Brockian.CosTraceNormThreeHundredSeventyNine
