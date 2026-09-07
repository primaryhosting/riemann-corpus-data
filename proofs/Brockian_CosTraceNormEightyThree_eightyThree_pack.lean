/-
  Brockian/CosTraceNormEightyThree.lean — spectral generator at p = 83.

  [ℚ(2 cos 2π/83):ℚ] = 41 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormEightyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_eightyThree : Nat.Prime 83 := by decide

theorem eightyThree_ne_two : (83 : ℕ) ≠ 2 := by decide

theorem degree_eightyThree : (minpoly ℚ (spectralGen 83)).natDegree = 41 :=
  real_subfield_degree prime_eightyThree eightyThree_ne_two

theorem isIntegral_spectralGen_eightyThree : IsIntegral ℤ (spectralGen 83) :=
  isIntegral_spectralGen prime_eightyThree

theorem isIntegral_spectralGen_eightyThree_Q : IsIntegral ℚ (spectralGen 83) :=
  isIntegral_spectralGen_ℚ prime_eightyThree

theorem isIntegral_and_degree_eightyThree :
    IsIntegral ℤ (spectralGen 83) ∧
      (minpoly ℚ (spectralGen 83)).natDegree = 41 :=
  ⟨isIntegral_spectralGen_eightyThree, degree_eightyThree⟩

theorem eightyThree_pack :
    IsIntegral ℤ (spectralGen 83) ∧
      (minpoly ℚ (spectralGen 83)).natDegree = 41 :=
  isIntegral_and_degree_eightyThree

end Brockian.CosTraceNormEightyThree
