/-
  Brockian/CosTraceNormFourHundredThirtyOne.lean — spectral generator at p = 431.

  [ℚ(2 cos 2π/431):ℚ] = 215 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFourHundredThirtyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fourHundredThirtyOne : Nat.Prime 431 := by decide

theorem fourHundredThirtyOne_ne_two : (431 : ℕ) ≠ 2 := by decide

theorem degree_fourHundredThirtyOne : (minpoly ℚ (spectralGen 431)).natDegree = 215 :=
  real_subfield_degree prime_fourHundredThirtyOne fourHundredThirtyOne_ne_two

theorem isIntegral_spectralGen_fourHundredThirtyOne : IsIntegral ℤ (spectralGen 431) :=
  isIntegral_spectralGen prime_fourHundredThirtyOne

theorem isIntegral_spectralGen_fourHundredThirtyOne_Q : IsIntegral ℚ (spectralGen 431) :=
  isIntegral_spectralGen_ℚ prime_fourHundredThirtyOne

theorem isIntegral_and_degree_fourHundredThirtyOne :
    IsIntegral ℤ (spectralGen 431) ∧
      (minpoly ℚ (spectralGen 431)).natDegree = 215 :=
  ⟨isIntegral_spectralGen_fourHundredThirtyOne, degree_fourHundredThirtyOne⟩

theorem fourHundredThirtyOne_pack :
    IsIntegral ℤ (spectralGen 431) ∧
      (minpoly ℚ (spectralGen 431)).natDegree = 215 :=
  isIntegral_and_degree_fourHundredThirtyOne

end Brockian.CosTraceNormFourHundredThirtyOne
