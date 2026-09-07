/-
  Brockian/CosTraceNormEightHundredEightyOne.lean — spectral generator at p = 881.

  [ℚ(2 cos 2π/881):ℚ] = 440 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormEightHundredEightyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_eightHundredEightyOne : Nat.Prime 881 := by decide

theorem eightHundredEightyOne_ne_two : (881 : ℕ) ≠ 2 := by decide

theorem degree_eightHundredEightyOne : (minpoly ℚ (spectralGen 881)).natDegree = 440 :=
  real_subfield_degree prime_eightHundredEightyOne eightHundredEightyOne_ne_two

theorem isIntegral_spectralGen_eightHundredEightyOne : IsIntegral ℤ (spectralGen 881) :=
  isIntegral_spectralGen prime_eightHundredEightyOne

theorem isIntegral_spectralGen_eightHundredEightyOne_Q : IsIntegral ℚ (spectralGen 881) :=
  isIntegral_spectralGen_ℚ prime_eightHundredEightyOne

theorem isIntegral_and_degree_eightHundredEightyOne :
    IsIntegral ℤ (spectralGen 881) ∧
      (minpoly ℚ (spectralGen 881)).natDegree = 440 :=
  ⟨isIntegral_spectralGen_eightHundredEightyOne, degree_eightHundredEightyOne⟩

theorem eightHundredEightyOne_pack :
    IsIntegral ℤ (spectralGen 881) ∧
      (minpoly ℚ (spectralGen 881)).natDegree = 440 :=
  isIntegral_and_degree_eightHundredEightyOne

end Brockian.CosTraceNormEightHundredEightyOne
