/-
  Brockian/CosTraceNormOneThousandFiftyOne.lean — spectral generator at p = 1051.

  [ℚ(2 cos 2π/1051):ℚ] = 525 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneThousandFiftyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneThousandFiftyOne : Nat.Prime 1051 := by decide

theorem oneThousandFiftyOne_ne_two : (1051 : ℕ) ≠ 2 := by decide

theorem degree_oneThousandFiftyOne : (minpoly ℚ (spectralGen 1051)).natDegree = 525 :=
  real_subfield_degree prime_oneThousandFiftyOne oneThousandFiftyOne_ne_two

theorem isIntegral_spectralGen_oneThousandFiftyOne : IsIntegral ℤ (spectralGen 1051) :=
  isIntegral_spectralGen prime_oneThousandFiftyOne

theorem isIntegral_spectralGen_oneThousandFiftyOne_Q : IsIntegral ℚ (spectralGen 1051) :=
  isIntegral_spectralGen_ℚ prime_oneThousandFiftyOne

theorem isIntegral_and_degree_oneThousandFiftyOne :
    IsIntegral ℤ (spectralGen 1051) ∧
      (minpoly ℚ (spectralGen 1051)).natDegree = 525 :=
  ⟨isIntegral_spectralGen_oneThousandFiftyOne, degree_oneThousandFiftyOne⟩

theorem oneThousandFiftyOne_pack :
    IsIntegral ℤ (spectralGen 1051) ∧
      (minpoly ℚ (spectralGen 1051)).natDegree = 525 :=
  isIntegral_and_degree_oneThousandFiftyOne

end Brockian.CosTraceNormOneThousandFiftyOne
