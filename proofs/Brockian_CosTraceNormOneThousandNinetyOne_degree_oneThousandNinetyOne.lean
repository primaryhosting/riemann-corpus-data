/-
  Brockian/CosTraceNormOneThousandNinetyOne.lean — spectral generator at p = 1091.

  [ℚ(2 cos 2π/1091):ℚ] = 545 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneThousandNinetyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneThousandNinetyOne : Nat.Prime 1091 := by decide

theorem oneThousandNinetyOne_ne_two : (1091 : ℕ) ≠ 2 := by decide

theorem degree_oneThousandNinetyOne : (minpoly ℚ (spectralGen 1091)).natDegree = 545 :=
  real_subfield_degree prime_oneThousandNinetyOne oneThousandNinetyOne_ne_two

theorem isIntegral_spectralGen_oneThousandNinetyOne : IsIntegral ℤ (spectralGen 1091) :=
  isIntegral_spectralGen prime_oneThousandNinetyOne

theorem isIntegral_spectralGen_oneThousandNinetyOne_Q : IsIntegral ℚ (spectralGen 1091) :=
  isIntegral_spectralGen_ℚ prime_oneThousandNinetyOne

theorem isIntegral_and_degree_oneThousandNinetyOne :
    IsIntegral ℤ (spectralGen 1091) ∧
      (minpoly ℚ (spectralGen 1091)).natDegree = 545 :=
  ⟨isIntegral_spectralGen_oneThousandNinetyOne, degree_oneThousandNinetyOne⟩

theorem oneThousandNinetyOne_pack :
    IsIntegral ℤ (spectralGen 1091) ∧
      (minpoly ℚ (spectralGen 1091)).natDegree = 545 :=
  isIntegral_and_degree_oneThousandNinetyOne

end Brockian.CosTraceNormOneThousandNinetyOne
