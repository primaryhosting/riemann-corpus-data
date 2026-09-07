/-
  Brockian/CosTraceNormOneThousandEightySeven.lean — spectral generator at p = 1087.

  [ℚ(2 cos 2π/1087):ℚ] = 543 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneThousandEightySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneThousandEightySeven : Nat.Prime 1087 := by decide

theorem oneThousandEightySeven_ne_two : (1087 : ℕ) ≠ 2 := by decide

theorem degree_oneThousandEightySeven : (minpoly ℚ (spectralGen 1087)).natDegree = 543 :=
  real_subfield_degree prime_oneThousandEightySeven oneThousandEightySeven_ne_two

theorem isIntegral_spectralGen_oneThousandEightySeven : IsIntegral ℤ (spectralGen 1087) :=
  isIntegral_spectralGen prime_oneThousandEightySeven

theorem isIntegral_spectralGen_oneThousandEightySeven_Q : IsIntegral ℚ (spectralGen 1087) :=
  isIntegral_spectralGen_ℚ prime_oneThousandEightySeven

theorem isIntegral_and_degree_oneThousandEightySeven :
    IsIntegral ℤ (spectralGen 1087) ∧
      (minpoly ℚ (spectralGen 1087)).natDegree = 543 :=
  ⟨isIntegral_spectralGen_oneThousandEightySeven, degree_oneThousandEightySeven⟩

theorem oneThousandEightySeven_pack :
    IsIntegral ℤ (spectralGen 1087) ∧
      (minpoly ℚ (spectralGen 1087)).natDegree = 543 :=
  isIntegral_and_degree_oneThousandEightySeven

end Brockian.CosTraceNormOneThousandEightySeven
