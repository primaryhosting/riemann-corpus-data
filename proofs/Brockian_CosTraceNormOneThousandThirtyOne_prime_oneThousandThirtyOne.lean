/-
  Brockian/CosTraceNormOneThousandThirtyOne.lean — spectral generator at p = 1031.

  [ℚ(2 cos 2π/1031):ℚ] = 515 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneThousandThirtyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneThousandThirtyOne : Nat.Prime 1031 := by decide

theorem oneThousandThirtyOne_ne_two : (1031 : ℕ) ≠ 2 := by decide

theorem degree_oneThousandThirtyOne : (minpoly ℚ (spectralGen 1031)).natDegree = 515 :=
  real_subfield_degree prime_oneThousandThirtyOne oneThousandThirtyOne_ne_two

theorem isIntegral_spectralGen_oneThousandThirtyOne : IsIntegral ℤ (spectralGen 1031) :=
  isIntegral_spectralGen prime_oneThousandThirtyOne

theorem isIntegral_spectralGen_oneThousandThirtyOne_Q : IsIntegral ℚ (spectralGen 1031) :=
  isIntegral_spectralGen_ℚ prime_oneThousandThirtyOne

theorem isIntegral_and_degree_oneThousandThirtyOne :
    IsIntegral ℤ (spectralGen 1031) ∧
      (minpoly ℚ (spectralGen 1031)).natDegree = 515 :=
  ⟨isIntegral_spectralGen_oneThousandThirtyOne, degree_oneThousandThirtyOne⟩

theorem oneThousandThirtyOne_pack :
    IsIntegral ℤ (spectralGen 1031) ∧
      (minpoly ℚ (spectralGen 1031)).natDegree = 515 :=
  isIntegral_and_degree_oneThousandThirtyOne

end Brockian.CosTraceNormOneThousandThirtyOne
