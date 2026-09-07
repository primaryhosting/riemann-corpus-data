/-
  Brockian/CosTraceNormOneThousandThirtyNine.lean — spectral generator at p = 1039.

  [ℚ(2 cos 2π/1039):ℚ] = 519 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneThousandThirtyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneThousandThirtyNine : Nat.Prime 1039 := by decide

theorem oneThousandThirtyNine_ne_two : (1039 : ℕ) ≠ 2 := by decide

theorem degree_oneThousandThirtyNine : (minpoly ℚ (spectralGen 1039)).natDegree = 519 :=
  real_subfield_degree prime_oneThousandThirtyNine oneThousandThirtyNine_ne_two

theorem isIntegral_spectralGen_oneThousandThirtyNine : IsIntegral ℤ (spectralGen 1039) :=
  isIntegral_spectralGen prime_oneThousandThirtyNine

theorem isIntegral_spectralGen_oneThousandThirtyNine_Q : IsIntegral ℚ (spectralGen 1039) :=
  isIntegral_spectralGen_ℚ prime_oneThousandThirtyNine

theorem isIntegral_and_degree_oneThousandThirtyNine :
    IsIntegral ℤ (spectralGen 1039) ∧
      (minpoly ℚ (spectralGen 1039)).natDegree = 519 :=
  ⟨isIntegral_spectralGen_oneThousandThirtyNine, degree_oneThousandThirtyNine⟩

theorem oneThousandThirtyNine_pack :
    IsIntegral ℤ (spectralGen 1039) ∧
      (minpoly ℚ (spectralGen 1039)).natDegree = 519 :=
  isIntegral_and_degree_oneThousandThirtyNine

end Brockian.CosTraceNormOneThousandThirtyNine
