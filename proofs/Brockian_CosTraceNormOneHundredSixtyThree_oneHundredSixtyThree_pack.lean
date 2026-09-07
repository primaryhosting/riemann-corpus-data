/-
  Brockian/CosTraceNormOneHundredSixtyThree.lean — spectral generator at p = 163.

  [ℚ(2 cos 2π/163):ℚ] = 81 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneHundredSixtyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredSixtyThree : Nat.Prime 163 := by decide

theorem oneHundredSixtyThree_ne_two : (163 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredSixtyThree : (minpoly ℚ (spectralGen 163)).natDegree = 81 :=
  real_subfield_degree prime_oneHundredSixtyThree oneHundredSixtyThree_ne_two

theorem isIntegral_spectralGen_oneHundredSixtyThree : IsIntegral ℤ (spectralGen 163) :=
  isIntegral_spectralGen prime_oneHundredSixtyThree

theorem isIntegral_spectralGen_oneHundredSixtyThree_Q : IsIntegral ℚ (spectralGen 163) :=
  isIntegral_spectralGen_ℚ prime_oneHundredSixtyThree

theorem isIntegral_and_degree_oneHundredSixtyThree :
    IsIntegral ℤ (spectralGen 163) ∧
      (minpoly ℚ (spectralGen 163)).natDegree = 81 :=
  ⟨isIntegral_spectralGen_oneHundredSixtyThree, degree_oneHundredSixtyThree⟩

theorem oneHundredSixtyThree_pack :
    IsIntegral ℤ (spectralGen 163) ∧
      (minpoly ℚ (spectralGen 163)).natDegree = 81 :=
  isIntegral_and_degree_oneHundredSixtyThree

end Brockian.CosTraceNormOneHundredSixtyThree
