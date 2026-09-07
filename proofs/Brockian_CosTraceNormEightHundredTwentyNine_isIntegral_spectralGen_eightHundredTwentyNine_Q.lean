/-
  Brockian/CosTraceNormEightHundredTwentyNine.lean — spectral generator at p = 829.

  [ℚ(2 cos 2π/829):ℚ] = 414 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormEightHundredTwentyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_eightHundredTwentyNine : Nat.Prime 829 := by decide

theorem eightHundredTwentyNine_ne_two : (829 : ℕ) ≠ 2 := by decide

theorem degree_eightHundredTwentyNine : (minpoly ℚ (spectralGen 829)).natDegree = 414 :=
  real_subfield_degree prime_eightHundredTwentyNine eightHundredTwentyNine_ne_two

theorem isIntegral_spectralGen_eightHundredTwentyNine : IsIntegral ℤ (spectralGen 829) :=
  isIntegral_spectralGen prime_eightHundredTwentyNine

theorem isIntegral_spectralGen_eightHundredTwentyNine_Q : IsIntegral ℚ (spectralGen 829) :=
  isIntegral_spectralGen_ℚ prime_eightHundredTwentyNine

theorem isIntegral_and_degree_eightHundredTwentyNine :
    IsIntegral ℤ (spectralGen 829) ∧
      (minpoly ℚ (spectralGen 829)).natDegree = 414 :=
  ⟨isIntegral_spectralGen_eightHundredTwentyNine, degree_eightHundredTwentyNine⟩

theorem eightHundredTwentyNine_pack :
    IsIntegral ℤ (spectralGen 829) ∧
      (minpoly ℚ (spectralGen 829)).natDegree = 414 :=
  isIntegral_and_degree_eightHundredTwentyNine

end Brockian.CosTraceNormEightHundredTwentyNine
