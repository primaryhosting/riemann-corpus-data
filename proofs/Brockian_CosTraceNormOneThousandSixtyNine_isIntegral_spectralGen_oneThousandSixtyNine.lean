/-
  Brockian/CosTraceNormOneThousandSixtyNine.lean — spectral generator at p = 1069.

  [ℚ(2 cos 2π/1069):ℚ] = 534 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneThousandSixtyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneThousandSixtyNine : Nat.Prime 1069 := by decide

theorem oneThousandSixtyNine_ne_two : (1069 : ℕ) ≠ 2 := by decide

theorem degree_oneThousandSixtyNine : (minpoly ℚ (spectralGen 1069)).natDegree = 534 :=
  real_subfield_degree prime_oneThousandSixtyNine oneThousandSixtyNine_ne_two

theorem isIntegral_spectralGen_oneThousandSixtyNine : IsIntegral ℤ (spectralGen 1069) :=
  isIntegral_spectralGen prime_oneThousandSixtyNine

theorem isIntegral_spectralGen_oneThousandSixtyNine_Q : IsIntegral ℚ (spectralGen 1069) :=
  isIntegral_spectralGen_ℚ prime_oneThousandSixtyNine

theorem isIntegral_and_degree_oneThousandSixtyNine :
    IsIntegral ℤ (spectralGen 1069) ∧
      (minpoly ℚ (spectralGen 1069)).natDegree = 534 :=
  ⟨isIntegral_spectralGen_oneThousandSixtyNine, degree_oneThousandSixtyNine⟩

theorem oneThousandSixtyNine_pack :
    IsIntegral ℤ (spectralGen 1069) ∧
      (minpoly ℚ (spectralGen 1069)).natDegree = 534 :=
  isIntegral_and_degree_oneThousandSixtyNine

end Brockian.CosTraceNormOneThousandSixtyNine
