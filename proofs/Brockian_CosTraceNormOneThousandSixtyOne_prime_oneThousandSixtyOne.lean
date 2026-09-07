/-
  Brockian/CosTraceNormOneThousandSixtyOne.lean — spectral generator at p = 1061.

  [ℚ(2 cos 2π/1061):ℚ] = 530 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneThousandSixtyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneThousandSixtyOne : Nat.Prime 1061 := by decide

theorem oneThousandSixtyOne_ne_two : (1061 : ℕ) ≠ 2 := by decide

theorem degree_oneThousandSixtyOne : (minpoly ℚ (spectralGen 1061)).natDegree = 530 :=
  real_subfield_degree prime_oneThousandSixtyOne oneThousandSixtyOne_ne_two

theorem isIntegral_spectralGen_oneThousandSixtyOne : IsIntegral ℤ (spectralGen 1061) :=
  isIntegral_spectralGen prime_oneThousandSixtyOne

theorem isIntegral_spectralGen_oneThousandSixtyOne_Q : IsIntegral ℚ (spectralGen 1061) :=
  isIntegral_spectralGen_ℚ prime_oneThousandSixtyOne

theorem isIntegral_and_degree_oneThousandSixtyOne :
    IsIntegral ℤ (spectralGen 1061) ∧
      (minpoly ℚ (spectralGen 1061)).natDegree = 530 :=
  ⟨isIntegral_spectralGen_oneThousandSixtyOne, degree_oneThousandSixtyOne⟩

theorem oneThousandSixtyOne_pack :
    IsIntegral ℤ (spectralGen 1061) ∧
      (minpoly ℚ (spectralGen 1061)).natDegree = 530 :=
  isIntegral_and_degree_oneThousandSixtyOne

end Brockian.CosTraceNormOneThousandSixtyOne
