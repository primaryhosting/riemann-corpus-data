/-
  Brockian/CosTraceNormOneThousandSixtyThree.lean — spectral generator at p = 1063.

  [ℚ(2 cos 2π/1063):ℚ] = 531 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneThousandSixtyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneThousandSixtyThree : Nat.Prime 1063 := by decide

theorem oneThousandSixtyThree_ne_two : (1063 : ℕ) ≠ 2 := by decide

theorem degree_oneThousandSixtyThree : (minpoly ℚ (spectralGen 1063)).natDegree = 531 :=
  real_subfield_degree prime_oneThousandSixtyThree oneThousandSixtyThree_ne_two

theorem isIntegral_spectralGen_oneThousandSixtyThree : IsIntegral ℤ (spectralGen 1063) :=
  isIntegral_spectralGen prime_oneThousandSixtyThree

theorem isIntegral_spectralGen_oneThousandSixtyThree_Q : IsIntegral ℚ (spectralGen 1063) :=
  isIntegral_spectralGen_ℚ prime_oneThousandSixtyThree

theorem isIntegral_and_degree_oneThousandSixtyThree :
    IsIntegral ℤ (spectralGen 1063) ∧
      (minpoly ℚ (spectralGen 1063)).natDegree = 531 :=
  ⟨isIntegral_spectralGen_oneThousandSixtyThree, degree_oneThousandSixtyThree⟩

theorem oneThousandSixtyThree_pack :
    IsIntegral ℤ (spectralGen 1063) ∧
      (minpoly ℚ (spectralGen 1063)).natDegree = 531 :=
  isIntegral_and_degree_oneThousandSixtyThree

end Brockian.CosTraceNormOneThousandSixtyThree
