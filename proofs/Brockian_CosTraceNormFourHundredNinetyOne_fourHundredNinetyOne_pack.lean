/-
  Brockian/CosTraceNormFourHundredNinetyOne.lean — spectral generator at p = 491.

  [ℚ(2 cos 2π/491):ℚ] = 245 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFourHundredNinetyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fourHundredNinetyOne : Nat.Prime 491 := by decide

theorem fourHundredNinetyOne_ne_two : (491 : ℕ) ≠ 2 := by decide

theorem degree_fourHundredNinetyOne : (minpoly ℚ (spectralGen 491)).natDegree = 245 :=
  real_subfield_degree prime_fourHundredNinetyOne fourHundredNinetyOne_ne_two

theorem isIntegral_spectralGen_fourHundredNinetyOne : IsIntegral ℤ (spectralGen 491) :=
  isIntegral_spectralGen prime_fourHundredNinetyOne

theorem isIntegral_spectralGen_fourHundredNinetyOne_Q : IsIntegral ℚ (spectralGen 491) :=
  isIntegral_spectralGen_ℚ prime_fourHundredNinetyOne

theorem isIntegral_and_degree_fourHundredNinetyOne :
    IsIntegral ℤ (spectralGen 491) ∧
      (minpoly ℚ (spectralGen 491)).natDegree = 245 :=
  ⟨isIntegral_spectralGen_fourHundredNinetyOne, degree_fourHundredNinetyOne⟩

theorem fourHundredNinetyOne_pack :
    IsIntegral ℤ (spectralGen 491) ∧
      (minpoly ℚ (spectralGen 491)).natDegree = 245 :=
  isIntegral_and_degree_fourHundredNinetyOne

end Brockian.CosTraceNormFourHundredNinetyOne
