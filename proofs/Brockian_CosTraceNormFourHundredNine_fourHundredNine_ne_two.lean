/-
  Brockian/CosTraceNormFourHundredNine.lean — spectral generator at p = 409.

  [ℚ(2 cos 2π/409):ℚ] = 204 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFourHundredNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fourHundredNine : Nat.Prime 409 := by decide

theorem fourHundredNine_ne_two : (409 : ℕ) ≠ 2 := by decide

theorem degree_fourHundredNine : (minpoly ℚ (spectralGen 409)).natDegree = 204 :=
  real_subfield_degree prime_fourHundredNine fourHundredNine_ne_two

theorem isIntegral_spectralGen_fourHundredNine : IsIntegral ℤ (spectralGen 409) :=
  isIntegral_spectralGen prime_fourHundredNine

theorem isIntegral_spectralGen_fourHundredNine_Q : IsIntegral ℚ (spectralGen 409) :=
  isIntegral_spectralGen_ℚ prime_fourHundredNine

theorem isIntegral_and_degree_fourHundredNine :
    IsIntegral ℤ (spectralGen 409) ∧
      (minpoly ℚ (spectralGen 409)).natDegree = 204 :=
  ⟨isIntegral_spectralGen_fourHundredNine, degree_fourHundredNine⟩

theorem fourHundredNine_pack :
    IsIntegral ℤ (spectralGen 409) ∧
      (minpoly ℚ (spectralGen 409)).natDegree = 204 :=
  isIntegral_and_degree_fourHundredNine

end Brockian.CosTraceNormFourHundredNine
