/-
  Brockian/CosTraceNormNineHundredTwentyNine.lean — spectral generator at p = 929.

  [ℚ(2 cos 2π/929):ℚ] = 464 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormNineHundredTwentyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_nineHundredTwentyNine : Nat.Prime 929 := by decide

theorem nineHundredTwentyNine_ne_two : (929 : ℕ) ≠ 2 := by decide

theorem degree_nineHundredTwentyNine : (minpoly ℚ (spectralGen 929)).natDegree = 464 :=
  real_subfield_degree prime_nineHundredTwentyNine nineHundredTwentyNine_ne_two

theorem isIntegral_spectralGen_nineHundredTwentyNine : IsIntegral ℤ (spectralGen 929) :=
  isIntegral_spectralGen prime_nineHundredTwentyNine

theorem isIntegral_spectralGen_nineHundredTwentyNine_Q : IsIntegral ℚ (spectralGen 929) :=
  isIntegral_spectralGen_ℚ prime_nineHundredTwentyNine

theorem isIntegral_and_degree_nineHundredTwentyNine :
    IsIntegral ℤ (spectralGen 929) ∧
      (minpoly ℚ (spectralGen 929)).natDegree = 464 :=
  ⟨isIntegral_spectralGen_nineHundredTwentyNine, degree_nineHundredTwentyNine⟩

theorem nineHundredTwentyNine_pack :
    IsIntegral ℤ (spectralGen 929) ∧
      (minpoly ℚ (spectralGen 929)).natDegree = 464 :=
  isIntegral_and_degree_nineHundredTwentyNine

end Brockian.CosTraceNormNineHundredTwentyNine
