/-
  Brockian/CosTraceNormFourHundredSixtySeven.lean — spectral generator at p = 467.

  [ℚ(2 cos 2π/467):ℚ] = 233 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFourHundredSixtySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fourHundredSixtySeven : Nat.Prime 467 := by decide

theorem fourHundredSixtySeven_ne_two : (467 : ℕ) ≠ 2 := by decide

theorem degree_fourHundredSixtySeven : (minpoly ℚ (spectralGen 467)).natDegree = 233 :=
  real_subfield_degree prime_fourHundredSixtySeven fourHundredSixtySeven_ne_two

theorem isIntegral_spectralGen_fourHundredSixtySeven : IsIntegral ℤ (spectralGen 467) :=
  isIntegral_spectralGen prime_fourHundredSixtySeven

theorem isIntegral_spectralGen_fourHundredSixtySeven_Q : IsIntegral ℚ (spectralGen 467) :=
  isIntegral_spectralGen_ℚ prime_fourHundredSixtySeven

theorem isIntegral_and_degree_fourHundredSixtySeven :
    IsIntegral ℤ (spectralGen 467) ∧
      (minpoly ℚ (spectralGen 467)).natDegree = 233 :=
  ⟨isIntegral_spectralGen_fourHundredSixtySeven, degree_fourHundredSixtySeven⟩

theorem fourHundredSixtySeven_pack :
    IsIntegral ℤ (spectralGen 467) ∧
      (minpoly ℚ (spectralGen 467)).natDegree = 233 :=
  isIntegral_and_degree_fourHundredSixtySeven

end Brockian.CosTraceNormFourHundredSixtySeven
