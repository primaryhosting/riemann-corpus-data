/-
  Brockian/CosTraceNormOneHundredSeventyThree.lean — spectral generator at p = 173.

  [ℚ(2 cos 2π/173):ℚ] = 86 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneHundredSeventyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredSeventyThree : Nat.Prime 173 := by decide

theorem oneHundredSeventyThree_ne_two : (173 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredSeventyThree : (minpoly ℚ (spectralGen 173)).natDegree = 86 :=
  real_subfield_degree prime_oneHundredSeventyThree oneHundredSeventyThree_ne_two

theorem isIntegral_spectralGen_oneHundredSeventyThree : IsIntegral ℤ (spectralGen 173) :=
  isIntegral_spectralGen prime_oneHundredSeventyThree

theorem isIntegral_spectralGen_oneHundredSeventyThree_Q : IsIntegral ℚ (spectralGen 173) :=
  isIntegral_spectralGen_ℚ prime_oneHundredSeventyThree

theorem isIntegral_and_degree_oneHundredSeventyThree :
    IsIntegral ℤ (spectralGen 173) ∧
      (minpoly ℚ (spectralGen 173)).natDegree = 86 :=
  ⟨isIntegral_spectralGen_oneHundredSeventyThree, degree_oneHundredSeventyThree⟩

theorem oneHundredSeventyThree_pack :
    IsIntegral ℤ (spectralGen 173) ∧
      (minpoly ℚ (spectralGen 173)).natDegree = 86 :=
  isIntegral_and_degree_oneHundredSeventyThree

end Brockian.CosTraceNormOneHundredSeventyThree
