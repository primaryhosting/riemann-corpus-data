/-
  Brockian/CosTraceNormEightHundredTwentyThree.lean — spectral generator at p = 823.

  [ℚ(2 cos 2π/823):ℚ] = 411 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormEightHundredTwentyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_eightHundredTwentyThree : Nat.Prime 823 := by decide

theorem eightHundredTwentyThree_ne_two : (823 : ℕ) ≠ 2 := by decide

theorem degree_eightHundredTwentyThree : (minpoly ℚ (spectralGen 823)).natDegree = 411 :=
  real_subfield_degree prime_eightHundredTwentyThree eightHundredTwentyThree_ne_two

theorem isIntegral_spectralGen_eightHundredTwentyThree : IsIntegral ℤ (spectralGen 823) :=
  isIntegral_spectralGen prime_eightHundredTwentyThree

theorem isIntegral_spectralGen_eightHundredTwentyThree_Q : IsIntegral ℚ (spectralGen 823) :=
  isIntegral_spectralGen_ℚ prime_eightHundredTwentyThree

theorem isIntegral_and_degree_eightHundredTwentyThree :
    IsIntegral ℤ (spectralGen 823) ∧
      (minpoly ℚ (spectralGen 823)).natDegree = 411 :=
  ⟨isIntegral_spectralGen_eightHundredTwentyThree, degree_eightHundredTwentyThree⟩

theorem eightHundredTwentyThree_pack :
    IsIntegral ℤ (spectralGen 823) ∧
      (minpoly ℚ (spectralGen 823)).natDegree = 411 :=
  isIntegral_and_degree_eightHundredTwentyThree

end Brockian.CosTraceNormEightHundredTwentyThree
