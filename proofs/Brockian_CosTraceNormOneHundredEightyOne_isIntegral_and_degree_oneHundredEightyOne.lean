/-
  Brockian/CosTraceNormOneHundredEightyOne.lean — spectral generator at p = 181.

  [ℚ(2 cos 2π/181):ℚ] = 90 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneHundredEightyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredEightyOne : Nat.Prime 181 := by decide

theorem oneHundredEightyOne_ne_two : (181 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredEightyOne : (minpoly ℚ (spectralGen 181)).natDegree = 90 :=
  real_subfield_degree prime_oneHundredEightyOne oneHundredEightyOne_ne_two

theorem isIntegral_spectralGen_oneHundredEightyOne : IsIntegral ℤ (spectralGen 181) :=
  isIntegral_spectralGen prime_oneHundredEightyOne

theorem isIntegral_spectralGen_oneHundredEightyOne_Q : IsIntegral ℚ (spectralGen 181) :=
  isIntegral_spectralGen_ℚ prime_oneHundredEightyOne

theorem isIntegral_and_degree_oneHundredEightyOne :
    IsIntegral ℤ (spectralGen 181) ∧
      (minpoly ℚ (spectralGen 181)).natDegree = 90 :=
  ⟨isIntegral_spectralGen_oneHundredEightyOne, degree_oneHundredEightyOne⟩

theorem oneHundredEightyOne_pack :
    IsIntegral ℤ (spectralGen 181) ∧
      (minpoly ℚ (spectralGen 181)).natDegree = 90 :=
  isIntegral_and_degree_oneHundredEightyOne

end Brockian.CosTraceNormOneHundredEightyOne
