/-
  Brockian/CosTraceNormOneThousandThirteen.lean — spectral generator at p = 1013.

  [ℚ(2 cos 2π/1013):ℚ] = 506 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneThousandThirteen

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneThousandThirteen : Nat.Prime 1013 := by decide

theorem oneThousandThirteen_ne_two : (1013 : ℕ) ≠ 2 := by decide

theorem degree_oneThousandThirteen : (minpoly ℚ (spectralGen 1013)).natDegree = 506 :=
  real_subfield_degree prime_oneThousandThirteen oneThousandThirteen_ne_two

theorem isIntegral_spectralGen_oneThousandThirteen : IsIntegral ℤ (spectralGen 1013) :=
  isIntegral_spectralGen prime_oneThousandThirteen

theorem isIntegral_spectralGen_oneThousandThirteen_Q : IsIntegral ℚ (spectralGen 1013) :=
  isIntegral_spectralGen_ℚ prime_oneThousandThirteen

theorem isIntegral_and_degree_oneThousandThirteen :
    IsIntegral ℤ (spectralGen 1013) ∧
      (minpoly ℚ (spectralGen 1013)).natDegree = 506 :=
  ⟨isIntegral_spectralGen_oneThousandThirteen, degree_oneThousandThirteen⟩

theorem oneThousandThirteen_pack :
    IsIntegral ℤ (spectralGen 1013) ∧
      (minpoly ℚ (spectralGen 1013)).natDegree = 506 :=
  isIntegral_and_degree_oneThousandThirteen

end Brockian.CosTraceNormOneThousandThirteen
