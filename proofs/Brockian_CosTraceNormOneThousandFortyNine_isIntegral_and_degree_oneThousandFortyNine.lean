/-
  Brockian/CosTraceNormOneThousandFortyNine.lean — spectral generator at p = 1049.

  [ℚ(2 cos 2π/1049):ℚ] = 524 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneThousandFortyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneThousandFortyNine : Nat.Prime 1049 := by decide

theorem oneThousandFortyNine_ne_two : (1049 : ℕ) ≠ 2 := by decide

theorem degree_oneThousandFortyNine : (minpoly ℚ (spectralGen 1049)).natDegree = 524 :=
  real_subfield_degree prime_oneThousandFortyNine oneThousandFortyNine_ne_two

theorem isIntegral_spectralGen_oneThousandFortyNine : IsIntegral ℤ (spectralGen 1049) :=
  isIntegral_spectralGen prime_oneThousandFortyNine

theorem isIntegral_spectralGen_oneThousandFortyNine_Q : IsIntegral ℚ (spectralGen 1049) :=
  isIntegral_spectralGen_ℚ prime_oneThousandFortyNine

theorem isIntegral_and_degree_oneThousandFortyNine :
    IsIntegral ℤ (spectralGen 1049) ∧
      (minpoly ℚ (spectralGen 1049)).natDegree = 524 :=
  ⟨isIntegral_spectralGen_oneThousandFortyNine, degree_oneThousandFortyNine⟩

theorem oneThousandFortyNine_pack :
    IsIntegral ℤ (spectralGen 1049) ∧
      (minpoly ℚ (spectralGen 1049)).natDegree = 524 :=
  isIntegral_and_degree_oneThousandFortyNine

end Brockian.CosTraceNormOneThousandFortyNine
