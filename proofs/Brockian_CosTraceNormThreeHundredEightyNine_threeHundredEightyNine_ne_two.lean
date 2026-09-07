/-
  Brockian/CosTraceNormThreeHundredEightyNine.lean — spectral generator at p = 389.

  [ℚ(2 cos 2π/389):ℚ] = 194 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormThreeHundredEightyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_threeHundredEightyNine : Nat.Prime 389 := by decide

theorem threeHundredEightyNine_ne_two : (389 : ℕ) ≠ 2 := by decide

theorem degree_threeHundredEightyNine : (minpoly ℚ (spectralGen 389)).natDegree = 194 :=
  real_subfield_degree prime_threeHundredEightyNine threeHundredEightyNine_ne_two

theorem isIntegral_spectralGen_threeHundredEightyNine : IsIntegral ℤ (spectralGen 389) :=
  isIntegral_spectralGen prime_threeHundredEightyNine

theorem isIntegral_spectralGen_threeHundredEightyNine_Q : IsIntegral ℚ (spectralGen 389) :=
  isIntegral_spectralGen_ℚ prime_threeHundredEightyNine

theorem isIntegral_and_degree_threeHundredEightyNine :
    IsIntegral ℤ (spectralGen 389) ∧
      (minpoly ℚ (spectralGen 389)).natDegree = 194 :=
  ⟨isIntegral_spectralGen_threeHundredEightyNine, degree_threeHundredEightyNine⟩

theorem threeHundredEightyNine_pack :
    IsIntegral ℤ (spectralGen 389) ∧
      (minpoly ℚ (spectralGen 389)).natDegree = 194 :=
  isIntegral_and_degree_threeHundredEightyNine

end Brockian.CosTraceNormThreeHundredEightyNine
