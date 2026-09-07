/-
  Brockian/CosTraceNormNineHundredSeventyOne.lean — spectral generator at p = 971.

  [ℚ(2 cos 2π/971):ℚ] = 485 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormNineHundredSeventyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_nineHundredSeventyOne : Nat.Prime 971 := by decide

theorem nineHundredSeventyOne_ne_two : (971 : ℕ) ≠ 2 := by decide

theorem degree_nineHundredSeventyOne : (minpoly ℚ (spectralGen 971)).natDegree = 485 :=
  real_subfield_degree prime_nineHundredSeventyOne nineHundredSeventyOne_ne_two

theorem isIntegral_spectralGen_nineHundredSeventyOne : IsIntegral ℤ (spectralGen 971) :=
  isIntegral_spectralGen prime_nineHundredSeventyOne

theorem isIntegral_spectralGen_nineHundredSeventyOne_Q : IsIntegral ℚ (spectralGen 971) :=
  isIntegral_spectralGen_ℚ prime_nineHundredSeventyOne

theorem isIntegral_and_degree_nineHundredSeventyOne :
    IsIntegral ℤ (spectralGen 971) ∧
      (minpoly ℚ (spectralGen 971)).natDegree = 485 :=
  ⟨isIntegral_spectralGen_nineHundredSeventyOne, degree_nineHundredSeventyOne⟩

theorem nineHundredSeventyOne_pack :
    IsIntegral ℤ (spectralGen 971) ∧
      (minpoly ℚ (spectralGen 971)).natDegree = 485 :=
  isIntegral_and_degree_nineHundredSeventyOne

end Brockian.CosTraceNormNineHundredSeventyOne
