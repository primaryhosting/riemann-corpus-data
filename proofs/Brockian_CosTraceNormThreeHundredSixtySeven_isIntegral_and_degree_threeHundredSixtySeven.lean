/-
  Brockian/CosTraceNormThreeHundredSixtySeven.lean — spectral generator at p = 367.

  [ℚ(2 cos 2π/367):ℚ] = 183 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormThreeHundredSixtySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_threeHundredSixtySeven : Nat.Prime 367 := by decide

theorem threeHundredSixtySeven_ne_two : (367 : ℕ) ≠ 2 := by decide

theorem degree_threeHundredSixtySeven : (minpoly ℚ (spectralGen 367)).natDegree = 183 :=
  real_subfield_degree prime_threeHundredSixtySeven threeHundredSixtySeven_ne_two

theorem isIntegral_spectralGen_threeHundredSixtySeven : IsIntegral ℤ (spectralGen 367) :=
  isIntegral_spectralGen prime_threeHundredSixtySeven

theorem isIntegral_spectralGen_threeHundredSixtySeven_Q : IsIntegral ℚ (spectralGen 367) :=
  isIntegral_spectralGen_ℚ prime_threeHundredSixtySeven

theorem isIntegral_and_degree_threeHundredSixtySeven :
    IsIntegral ℤ (spectralGen 367) ∧
      (minpoly ℚ (spectralGen 367)).natDegree = 183 :=
  ⟨isIntegral_spectralGen_threeHundredSixtySeven, degree_threeHundredSixtySeven⟩

theorem threeHundredSixtySeven_pack :
    IsIntegral ℤ (spectralGen 367) ∧
      (minpoly ℚ (spectralGen 367)).natDegree = 183 :=
  isIntegral_and_degree_threeHundredSixtySeven

end Brockian.CosTraceNormThreeHundredSixtySeven
