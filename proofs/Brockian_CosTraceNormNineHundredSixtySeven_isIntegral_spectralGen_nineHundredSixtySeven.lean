/-
  Brockian/CosTraceNormNineHundredSixtySeven.lean — spectral generator at p = 967.

  [ℚ(2 cos 2π/967):ℚ] = 483 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormNineHundredSixtySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_nineHundredSixtySeven : Nat.Prime 967 := by decide

theorem nineHundredSixtySeven_ne_two : (967 : ℕ) ≠ 2 := by decide

theorem degree_nineHundredSixtySeven : (minpoly ℚ (spectralGen 967)).natDegree = 483 :=
  real_subfield_degree prime_nineHundredSixtySeven nineHundredSixtySeven_ne_two

theorem isIntegral_spectralGen_nineHundredSixtySeven : IsIntegral ℤ (spectralGen 967) :=
  isIntegral_spectralGen prime_nineHundredSixtySeven

theorem isIntegral_spectralGen_nineHundredSixtySeven_Q : IsIntegral ℚ (spectralGen 967) :=
  isIntegral_spectralGen_ℚ prime_nineHundredSixtySeven

theorem isIntegral_and_degree_nineHundredSixtySeven :
    IsIntegral ℤ (spectralGen 967) ∧
      (minpoly ℚ (spectralGen 967)).natDegree = 483 :=
  ⟨isIntegral_spectralGen_nineHundredSixtySeven, degree_nineHundredSixtySeven⟩

theorem nineHundredSixtySeven_pack :
    IsIntegral ℤ (spectralGen 967) ∧
      (minpoly ℚ (spectralGen 967)).natDegree = 483 :=
  isIntegral_and_degree_nineHundredSixtySeven

end Brockian.CosTraceNormNineHundredSixtySeven
