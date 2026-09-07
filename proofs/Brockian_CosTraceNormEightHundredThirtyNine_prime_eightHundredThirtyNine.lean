/-
  Brockian/CosTraceNormEightHundredThirtyNine.lean — spectral generator at p = 839.

  [ℚ(2 cos 2π/839):ℚ] = 419 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormEightHundredThirtyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_eightHundredThirtyNine : Nat.Prime 839 := by decide

theorem eightHundredThirtyNine_ne_two : (839 : ℕ) ≠ 2 := by decide

theorem degree_eightHundredThirtyNine : (minpoly ℚ (spectralGen 839)).natDegree = 419 :=
  real_subfield_degree prime_eightHundredThirtyNine eightHundredThirtyNine_ne_two

theorem isIntegral_spectralGen_eightHundredThirtyNine : IsIntegral ℤ (spectralGen 839) :=
  isIntegral_spectralGen prime_eightHundredThirtyNine

theorem isIntegral_spectralGen_eightHundredThirtyNine_Q : IsIntegral ℚ (spectralGen 839) :=
  isIntegral_spectralGen_ℚ prime_eightHundredThirtyNine

theorem isIntegral_and_degree_eightHundredThirtyNine :
    IsIntegral ℤ (spectralGen 839) ∧
      (minpoly ℚ (spectralGen 839)).natDegree = 419 :=
  ⟨isIntegral_spectralGen_eightHundredThirtyNine, degree_eightHundredThirtyNine⟩

theorem eightHundredThirtyNine_pack :
    IsIntegral ℤ (spectralGen 839) ∧
      (minpoly ℚ (spectralGen 839)).natDegree = 419 :=
  isIntegral_and_degree_eightHundredThirtyNine

end Brockian.CosTraceNormEightHundredThirtyNine
