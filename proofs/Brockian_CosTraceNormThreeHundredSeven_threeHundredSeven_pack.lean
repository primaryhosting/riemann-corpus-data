/-
  Brockian/CosTraceNormThreeHundredSeven.lean — spectral generator at p = 307.

  [ℚ(2 cos 2π/307):ℚ] = 153 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormThreeHundredSeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_threeHundredSeven : Nat.Prime 307 := by decide

theorem threeHundredSeven_ne_two : (307 : ℕ) ≠ 2 := by decide

theorem degree_threeHundredSeven : (minpoly ℚ (spectralGen 307)).natDegree = 153 :=
  real_subfield_degree prime_threeHundredSeven threeHundredSeven_ne_two

theorem isIntegral_spectralGen_threeHundredSeven : IsIntegral ℤ (spectralGen 307) :=
  isIntegral_spectralGen prime_threeHundredSeven

theorem isIntegral_spectralGen_threeHundredSeven_Q : IsIntegral ℚ (spectralGen 307) :=
  isIntegral_spectralGen_ℚ prime_threeHundredSeven

theorem isIntegral_and_degree_threeHundredSeven :
    IsIntegral ℤ (spectralGen 307) ∧
      (minpoly ℚ (spectralGen 307)).natDegree = 153 :=
  ⟨isIntegral_spectralGen_threeHundredSeven, degree_threeHundredSeven⟩

theorem threeHundredSeven_pack :
    IsIntegral ℤ (spectralGen 307) ∧
      (minpoly ℚ (spectralGen 307)).natDegree = 153 :=
  isIntegral_and_degree_threeHundredSeven

end Brockian.CosTraceNormThreeHundredSeven
