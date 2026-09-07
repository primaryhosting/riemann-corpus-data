/-
  Brockian/CosTraceNormOneThousandTwentyOne.lean — spectral generator at p = 1021.

  [ℚ(2 cos 2π/1021):ℚ] = 510 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneThousandTwentyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneThousandTwentyOne : Nat.Prime 1021 := by decide

theorem oneThousandTwentyOne_ne_two : (1021 : ℕ) ≠ 2 := by decide

theorem degree_oneThousandTwentyOne : (minpoly ℚ (spectralGen 1021)).natDegree = 510 :=
  real_subfield_degree prime_oneThousandTwentyOne oneThousandTwentyOne_ne_two

theorem isIntegral_spectralGen_oneThousandTwentyOne : IsIntegral ℤ (spectralGen 1021) :=
  isIntegral_spectralGen prime_oneThousandTwentyOne

theorem isIntegral_spectralGen_oneThousandTwentyOne_Q : IsIntegral ℚ (spectralGen 1021) :=
  isIntegral_spectralGen_ℚ prime_oneThousandTwentyOne

theorem isIntegral_and_degree_oneThousandTwentyOne :
    IsIntegral ℤ (spectralGen 1021) ∧
      (minpoly ℚ (spectralGen 1021)).natDegree = 510 :=
  ⟨isIntegral_spectralGen_oneThousandTwentyOne, degree_oneThousandTwentyOne⟩

theorem oneThousandTwentyOne_pack :
    IsIntegral ℤ (spectralGen 1021) ∧
      (minpoly ℚ (spectralGen 1021)).natDegree = 510 :=
  isIntegral_and_degree_oneThousandTwentyOne

end Brockian.CosTraceNormOneThousandTwentyOne
