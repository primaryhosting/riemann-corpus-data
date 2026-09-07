/-
  Brockian/CosTraceNormSevenHundredOne.lean — spectral generator at p = 701.

  [ℚ(2 cos 2π/701):ℚ] = 350 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSevenHundredOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sevenHundredOne : Nat.Prime 701 := by decide

theorem sevenHundredOne_ne_two : (701 : ℕ) ≠ 2 := by decide

theorem degree_sevenHundredOne : (minpoly ℚ (spectralGen 701)).natDegree = 350 :=
  real_subfield_degree prime_sevenHundredOne sevenHundredOne_ne_two

theorem isIntegral_spectralGen_sevenHundredOne : IsIntegral ℤ (spectralGen 701) :=
  isIntegral_spectralGen prime_sevenHundredOne

theorem isIntegral_spectralGen_sevenHundredOne_Q : IsIntegral ℚ (spectralGen 701) :=
  isIntegral_spectralGen_ℚ prime_sevenHundredOne

theorem isIntegral_and_degree_sevenHundredOne :
    IsIntegral ℤ (spectralGen 701) ∧
      (minpoly ℚ (spectralGen 701)).natDegree = 350 :=
  ⟨isIntegral_spectralGen_sevenHundredOne, degree_sevenHundredOne⟩

theorem sevenHundredOne_pack :
    IsIntegral ℤ (spectralGen 701) ∧
      (minpoly ℚ (spectralGen 701)).natDegree = 350 :=
  isIntegral_and_degree_sevenHundredOne

end Brockian.CosTraceNormSevenHundredOne
