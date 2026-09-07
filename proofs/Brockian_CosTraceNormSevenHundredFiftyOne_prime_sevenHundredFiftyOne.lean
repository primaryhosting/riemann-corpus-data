/-
  Brockian/CosTraceNormSevenHundredFiftyOne.lean — spectral generator at p = 751.

  [ℚ(2 cos 2π/751):ℚ] = 375 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSevenHundredFiftyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sevenHundredFiftyOne : Nat.Prime 751 := by decide

theorem sevenHundredFiftyOne_ne_two : (751 : ℕ) ≠ 2 := by decide

theorem degree_sevenHundredFiftyOne : (minpoly ℚ (spectralGen 751)).natDegree = 375 :=
  real_subfield_degree prime_sevenHundredFiftyOne sevenHundredFiftyOne_ne_two

theorem isIntegral_spectralGen_sevenHundredFiftyOne : IsIntegral ℤ (spectralGen 751) :=
  isIntegral_spectralGen prime_sevenHundredFiftyOne

theorem isIntegral_spectralGen_sevenHundredFiftyOne_Q : IsIntegral ℚ (spectralGen 751) :=
  isIntegral_spectralGen_ℚ prime_sevenHundredFiftyOne

theorem isIntegral_and_degree_sevenHundredFiftyOne :
    IsIntegral ℤ (spectralGen 751) ∧
      (minpoly ℚ (spectralGen 751)).natDegree = 375 :=
  ⟨isIntegral_spectralGen_sevenHundredFiftyOne, degree_sevenHundredFiftyOne⟩

theorem sevenHundredFiftyOne_pack :
    IsIntegral ℤ (spectralGen 751) ∧
      (minpoly ℚ (spectralGen 751)).natDegree = 375 :=
  isIntegral_and_degree_sevenHundredFiftyOne

end Brockian.CosTraceNormSevenHundredFiftyOne
