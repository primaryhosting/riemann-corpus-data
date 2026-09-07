/-
  Brockian/CosTraceNormOneHundredThree.lean — spectral generator at p = 103.

  [ℚ(2 cos 2π/103):ℚ] = 51 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormOneHundredThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredThree : Nat.Prime 103 := by decide

theorem oneHundredThree_ne_two : (103 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredThree : (minpoly ℚ (spectralGen 103)).natDegree = 51 :=
  real_subfield_degree prime_oneHundredThree oneHundredThree_ne_two

theorem isIntegral_spectralGen_oneHundredThree : IsIntegral ℤ (spectralGen 103) :=
  isIntegral_spectralGen prime_oneHundredThree

theorem isIntegral_spectralGen_oneHundredThree_Q : IsIntegral ℚ (spectralGen 103) :=
  isIntegral_spectralGen_ℚ prime_oneHundredThree

theorem isIntegral_and_degree_oneHundredThree :
    IsIntegral ℤ (spectralGen 103) ∧
      (minpoly ℚ (spectralGen 103)).natDegree = 51 :=
  ⟨isIntegral_spectralGen_oneHundredThree, degree_oneHundredThree⟩

theorem oneHundredThree_pack :
    IsIntegral ℤ (spectralGen 103) ∧
      (minpoly ℚ (spectralGen 103)).natDegree = 51 :=
  isIntegral_and_degree_oneHundredThree

end Brockian.CosTraceNormOneHundredThree
