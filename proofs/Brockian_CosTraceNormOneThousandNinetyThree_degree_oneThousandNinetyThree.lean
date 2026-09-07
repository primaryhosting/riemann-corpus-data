/-
  Brockian/CosTraceNormOneThousandNinetyThree.lean — spectral generator at p = 1093.

  [ℚ(2 cos 2π/1093):ℚ] = 546 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneThousandNinetyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneThousandNinetyThree : Nat.Prime 1093 := by decide

theorem oneThousandNinetyThree_ne_two : (1093 : ℕ) ≠ 2 := by decide

theorem degree_oneThousandNinetyThree : (minpoly ℚ (spectralGen 1093)).natDegree = 546 :=
  real_subfield_degree prime_oneThousandNinetyThree oneThousandNinetyThree_ne_two

theorem isIntegral_spectralGen_oneThousandNinetyThree : IsIntegral ℤ (spectralGen 1093) :=
  isIntegral_spectralGen prime_oneThousandNinetyThree

theorem isIntegral_spectralGen_oneThousandNinetyThree_Q : IsIntegral ℚ (spectralGen 1093) :=
  isIntegral_spectralGen_ℚ prime_oneThousandNinetyThree

theorem isIntegral_and_degree_oneThousandNinetyThree :
    IsIntegral ℤ (spectralGen 1093) ∧
      (minpoly ℚ (spectralGen 1093)).natDegree = 546 :=
  ⟨isIntegral_spectralGen_oneThousandNinetyThree, degree_oneThousandNinetyThree⟩

theorem oneThousandNinetyThree_pack :
    IsIntegral ℤ (spectralGen 1093) ∧
      (minpoly ℚ (spectralGen 1093)).natDegree = 546 :=
  isIntegral_and_degree_oneThousandNinetyThree

end Brockian.CosTraceNormOneThousandNinetyThree
