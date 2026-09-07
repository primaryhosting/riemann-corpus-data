/-
  Brockian/CosTraceNormOneThousandNineteen.lean — spectral generator at p = 1019.

  [ℚ(2 cos 2π/1019):ℚ] = 509 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneThousandNineteen

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneThousandNineteen : Nat.Prime 1019 := by decide

theorem oneThousandNineteen_ne_two : (1019 : ℕ) ≠ 2 := by decide

theorem degree_oneThousandNineteen : (minpoly ℚ (spectralGen 1019)).natDegree = 509 :=
  real_subfield_degree prime_oneThousandNineteen oneThousandNineteen_ne_two

theorem isIntegral_spectralGen_oneThousandNineteen : IsIntegral ℤ (spectralGen 1019) :=
  isIntegral_spectralGen prime_oneThousandNineteen

theorem isIntegral_spectralGen_oneThousandNineteen_Q : IsIntegral ℚ (spectralGen 1019) :=
  isIntegral_spectralGen_ℚ prime_oneThousandNineteen

theorem isIntegral_and_degree_oneThousandNineteen :
    IsIntegral ℤ (spectralGen 1019) ∧
      (minpoly ℚ (spectralGen 1019)).natDegree = 509 :=
  ⟨isIntegral_spectralGen_oneThousandNineteen, degree_oneThousandNineteen⟩

theorem oneThousandNineteen_pack :
    IsIntegral ℤ (spectralGen 1019) ∧
      (minpoly ℚ (spectralGen 1019)).natDegree = 509 :=
  isIntegral_and_degree_oneThousandNineteen

end Brockian.CosTraceNormOneThousandNineteen
