/-
  Brockian/CosTraceNormFourHundredOne.lean — spectral generator at p = 401.

  [ℚ(2 cos 2π/401):ℚ] = 200 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFourHundredOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fourHundredOne : Nat.Prime 401 := by decide

theorem fourHundredOne_ne_two : (401 : ℕ) ≠ 2 := by decide

theorem degree_fourHundredOne : (minpoly ℚ (spectralGen 401)).natDegree = 200 :=
  real_subfield_degree prime_fourHundredOne fourHundredOne_ne_two

theorem isIntegral_spectralGen_fourHundredOne : IsIntegral ℤ (spectralGen 401) :=
  isIntegral_spectralGen prime_fourHundredOne

theorem isIntegral_spectralGen_fourHundredOne_Q : IsIntegral ℚ (spectralGen 401) :=
  isIntegral_spectralGen_ℚ prime_fourHundredOne

theorem isIntegral_and_degree_fourHundredOne :
    IsIntegral ℤ (spectralGen 401) ∧
      (minpoly ℚ (spectralGen 401)).natDegree = 200 :=
  ⟨isIntegral_spectralGen_fourHundredOne, degree_fourHundredOne⟩

theorem fourHundredOne_pack :
    IsIntegral ℤ (spectralGen 401) ∧
      (minpoly ℚ (spectralGen 401)).natDegree = 200 :=
  isIntegral_and_degree_fourHundredOne

end Brockian.CosTraceNormFourHundredOne
