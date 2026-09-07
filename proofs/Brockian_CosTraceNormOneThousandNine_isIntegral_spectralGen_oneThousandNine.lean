/-
  Brockian/CosTraceNormOneThousandNine.lean — spectral generator at p = 1009.

  [ℚ(2 cos 2π/1009):ℚ] = 504 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneThousandNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneThousandNine : Nat.Prime 1009 := by decide

theorem oneThousandNine_ne_two : (1009 : ℕ) ≠ 2 := by decide

theorem degree_oneThousandNine : (minpoly ℚ (spectralGen 1009)).natDegree = 504 :=
  real_subfield_degree prime_oneThousandNine oneThousandNine_ne_two

theorem isIntegral_spectralGen_oneThousandNine : IsIntegral ℤ (spectralGen 1009) :=
  isIntegral_spectralGen prime_oneThousandNine

theorem isIntegral_spectralGen_oneThousandNine_Q : IsIntegral ℚ (spectralGen 1009) :=
  isIntegral_spectralGen_ℚ prime_oneThousandNine

theorem isIntegral_and_degree_oneThousandNine :
    IsIntegral ℤ (spectralGen 1009) ∧
      (minpoly ℚ (spectralGen 1009)).natDegree = 504 :=
  ⟨isIntegral_spectralGen_oneThousandNine, degree_oneThousandNine⟩

theorem oneThousandNine_pack :
    IsIntegral ℤ (spectralGen 1009) ∧
      (minpoly ℚ (spectralGen 1009)).natDegree = 504 :=
  isIntegral_and_degree_oneThousandNine

end Brockian.CosTraceNormOneThousandNine
