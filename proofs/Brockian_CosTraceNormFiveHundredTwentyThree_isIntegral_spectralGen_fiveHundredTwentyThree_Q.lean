/-
  Brockian/CosTraceNormFiveHundredTwentyThree.lean — spectral generator at p = 523.

  [ℚ(2 cos 2π/523):ℚ] = 261 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFiveHundredTwentyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fiveHundredTwentyThree : Nat.Prime 523 := by decide

theorem fiveHundredTwentyThree_ne_two : (523 : ℕ) ≠ 2 := by decide

theorem degree_fiveHundredTwentyThree : (minpoly ℚ (spectralGen 523)).natDegree = 261 :=
  real_subfield_degree prime_fiveHundredTwentyThree fiveHundredTwentyThree_ne_two

theorem isIntegral_spectralGen_fiveHundredTwentyThree : IsIntegral ℤ (spectralGen 523) :=
  isIntegral_spectralGen prime_fiveHundredTwentyThree

theorem isIntegral_spectralGen_fiveHundredTwentyThree_Q : IsIntegral ℚ (spectralGen 523) :=
  isIntegral_spectralGen_ℚ prime_fiveHundredTwentyThree

theorem isIntegral_and_degree_fiveHundredTwentyThree :
    IsIntegral ℤ (spectralGen 523) ∧
      (minpoly ℚ (spectralGen 523)).natDegree = 261 :=
  ⟨isIntegral_spectralGen_fiveHundredTwentyThree, degree_fiveHundredTwentyThree⟩

theorem fiveHundredTwentyThree_pack :
    IsIntegral ℤ (spectralGen 523) ∧
      (minpoly ℚ (spectralGen 523)).natDegree = 261 :=
  isIntegral_and_degree_fiveHundredTwentyThree

end Brockian.CosTraceNormFiveHundredTwentyThree
