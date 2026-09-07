/-
  Brockian/CosTraceNormTwoHundredTwentyThree.lean — spectral generator at p = 223.

  [ℚ(2 cos 2π/223):ℚ] = 111 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormTwoHundredTwentyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_twoHundredTwentyThree : Nat.Prime 223 := by decide

theorem twoHundredTwentyThree_ne_two : (223 : ℕ) ≠ 2 := by decide

theorem degree_twoHundredTwentyThree : (minpoly ℚ (spectralGen 223)).natDegree = 111 :=
  real_subfield_degree prime_twoHundredTwentyThree twoHundredTwentyThree_ne_two

theorem isIntegral_spectralGen_twoHundredTwentyThree : IsIntegral ℤ (spectralGen 223) :=
  isIntegral_spectralGen prime_twoHundredTwentyThree

theorem isIntegral_spectralGen_twoHundredTwentyThree_Q : IsIntegral ℚ (spectralGen 223) :=
  isIntegral_spectralGen_ℚ prime_twoHundredTwentyThree

theorem isIntegral_and_degree_twoHundredTwentyThree :
    IsIntegral ℤ (spectralGen 223) ∧
      (minpoly ℚ (spectralGen 223)).natDegree = 111 :=
  ⟨isIntegral_spectralGen_twoHundredTwentyThree, degree_twoHundredTwentyThree⟩

theorem twoHundredTwentyThree_pack :
    IsIntegral ℤ (spectralGen 223) ∧
      (minpoly ℚ (spectralGen 223)).natDegree = 111 :=
  isIntegral_and_degree_twoHundredTwentyThree

end Brockian.CosTraceNormTwoHundredTwentyThree
