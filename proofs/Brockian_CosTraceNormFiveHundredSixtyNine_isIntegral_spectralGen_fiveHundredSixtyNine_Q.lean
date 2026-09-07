/-
  Brockian/CosTraceNormFiveHundredSixtyNine.lean — spectral generator at p = 569.

  [ℚ(2 cos 2π/569):ℚ] = 284 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFiveHundredSixtyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fiveHundredSixtyNine : Nat.Prime 569 := by decide

theorem fiveHundredSixtyNine_ne_two : (569 : ℕ) ≠ 2 := by decide

theorem degree_fiveHundredSixtyNine : (minpoly ℚ (spectralGen 569)).natDegree = 284 :=
  real_subfield_degree prime_fiveHundredSixtyNine fiveHundredSixtyNine_ne_two

theorem isIntegral_spectralGen_fiveHundredSixtyNine : IsIntegral ℤ (spectralGen 569) :=
  isIntegral_spectralGen prime_fiveHundredSixtyNine

theorem isIntegral_spectralGen_fiveHundredSixtyNine_Q : IsIntegral ℚ (spectralGen 569) :=
  isIntegral_spectralGen_ℚ prime_fiveHundredSixtyNine

theorem isIntegral_and_degree_fiveHundredSixtyNine :
    IsIntegral ℤ (spectralGen 569) ∧
      (minpoly ℚ (spectralGen 569)).natDegree = 284 :=
  ⟨isIntegral_spectralGen_fiveHundredSixtyNine, degree_fiveHundredSixtyNine⟩

theorem fiveHundredSixtyNine_pack :
    IsIntegral ℤ (spectralGen 569) ∧
      (minpoly ℚ (spectralGen 569)).natDegree = 284 :=
  isIntegral_and_degree_fiveHundredSixtyNine

end Brockian.CosTraceNormFiveHundredSixtyNine
