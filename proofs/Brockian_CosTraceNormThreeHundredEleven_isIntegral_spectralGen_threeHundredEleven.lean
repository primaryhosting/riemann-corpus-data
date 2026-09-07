/-
  Brockian/CosTraceNormThreeHundredEleven.lean — spectral generator at p = 311.

  [ℚ(2 cos 2π/311):ℚ] = 155 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormThreeHundredEleven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_threeHundredEleven : Nat.Prime 311 := by decide

theorem threeHundredEleven_ne_two : (311 : ℕ) ≠ 2 := by decide

theorem degree_threeHundredEleven : (minpoly ℚ (spectralGen 311)).natDegree = 155 :=
  real_subfield_degree prime_threeHundredEleven threeHundredEleven_ne_two

theorem isIntegral_spectralGen_threeHundredEleven : IsIntegral ℤ (spectralGen 311) :=
  isIntegral_spectralGen prime_threeHundredEleven

theorem isIntegral_spectralGen_threeHundredEleven_Q : IsIntegral ℚ (spectralGen 311) :=
  isIntegral_spectralGen_ℚ prime_threeHundredEleven

theorem isIntegral_and_degree_threeHundredEleven :
    IsIntegral ℤ (spectralGen 311) ∧
      (minpoly ℚ (spectralGen 311)).natDegree = 155 :=
  ⟨isIntegral_spectralGen_threeHundredEleven, degree_threeHundredEleven⟩

theorem threeHundredEleven_pack :
    IsIntegral ℤ (spectralGen 311) ∧
      (minpoly ℚ (spectralGen 311)).natDegree = 155 :=
  isIntegral_and_degree_threeHundredEleven

end Brockian.CosTraceNormThreeHundredEleven
