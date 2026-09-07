/-
  Brockian/CosTraceNormSevenHundredSixtyOne.lean — spectral generator at p = 761.

  [ℚ(2 cos 2π/761):ℚ] = 380 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSevenHundredSixtyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sevenHundredSixtyOne : Nat.Prime 761 := by decide

theorem sevenHundredSixtyOne_ne_two : (761 : ℕ) ≠ 2 := by decide

theorem degree_sevenHundredSixtyOne : (minpoly ℚ (spectralGen 761)).natDegree = 380 :=
  real_subfield_degree prime_sevenHundredSixtyOne sevenHundredSixtyOne_ne_two

theorem isIntegral_spectralGen_sevenHundredSixtyOne : IsIntegral ℤ (spectralGen 761) :=
  isIntegral_spectralGen prime_sevenHundredSixtyOne

theorem isIntegral_spectralGen_sevenHundredSixtyOne_Q : IsIntegral ℚ (spectralGen 761) :=
  isIntegral_spectralGen_ℚ prime_sevenHundredSixtyOne

theorem isIntegral_and_degree_sevenHundredSixtyOne :
    IsIntegral ℤ (spectralGen 761) ∧
      (minpoly ℚ (spectralGen 761)).natDegree = 380 :=
  ⟨isIntegral_spectralGen_sevenHundredSixtyOne, degree_sevenHundredSixtyOne⟩

theorem sevenHundredSixtyOne_pack :
    IsIntegral ℤ (spectralGen 761) ∧
      (minpoly ℚ (spectralGen 761)).natDegree = 380 :=
  isIntegral_and_degree_sevenHundredSixtyOne

end Brockian.CosTraceNormSevenHundredSixtyOne
