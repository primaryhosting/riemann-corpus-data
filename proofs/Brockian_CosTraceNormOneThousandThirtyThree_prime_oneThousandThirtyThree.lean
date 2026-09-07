/-
  Brockian/CosTraceNormOneThousandThirtyThree.lean — spectral generator at p = 1033.

  [ℚ(2 cos 2π/1033):ℚ] = 516 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneThousandThirtyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneThousandThirtyThree : Nat.Prime 1033 := by decide

theorem oneThousandThirtyThree_ne_two : (1033 : ℕ) ≠ 2 := by decide

theorem degree_oneThousandThirtyThree : (minpoly ℚ (spectralGen 1033)).natDegree = 516 :=
  real_subfield_degree prime_oneThousandThirtyThree oneThousandThirtyThree_ne_two

theorem isIntegral_spectralGen_oneThousandThirtyThree : IsIntegral ℤ (spectralGen 1033) :=
  isIntegral_spectralGen prime_oneThousandThirtyThree

theorem isIntegral_spectralGen_oneThousandThirtyThree_Q : IsIntegral ℚ (spectralGen 1033) :=
  isIntegral_spectralGen_ℚ prime_oneThousandThirtyThree

theorem isIntegral_and_degree_oneThousandThirtyThree :
    IsIntegral ℤ (spectralGen 1033) ∧
      (minpoly ℚ (spectralGen 1033)).natDegree = 516 :=
  ⟨isIntegral_spectralGen_oneThousandThirtyThree, degree_oneThousandThirtyThree⟩

theorem oneThousandThirtyThree_pack :
    IsIntegral ℤ (spectralGen 1033) ∧
      (minpoly ℚ (spectralGen 1033)).natDegree = 516 :=
  isIntegral_and_degree_oneThousandThirtyThree

end Brockian.CosTraceNormOneThousandThirtyThree
