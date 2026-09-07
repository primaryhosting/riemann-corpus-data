/-
  Brockian/CosTraceNormFiveHundredSixtyThree.lean — spectral generator at p = 563.

  [ℚ(2 cos 2π/563):ℚ] = 281 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFiveHundredSixtyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fiveHundredSixtyThree : Nat.Prime 563 := by decide

theorem fiveHundredSixtyThree_ne_two : (563 : ℕ) ≠ 2 := by decide

theorem degree_fiveHundredSixtyThree : (minpoly ℚ (spectralGen 563)).natDegree = 281 :=
  real_subfield_degree prime_fiveHundredSixtyThree fiveHundredSixtyThree_ne_two

theorem isIntegral_spectralGen_fiveHundredSixtyThree : IsIntegral ℤ (spectralGen 563) :=
  isIntegral_spectralGen prime_fiveHundredSixtyThree

theorem isIntegral_spectralGen_fiveHundredSixtyThree_Q : IsIntegral ℚ (spectralGen 563) :=
  isIntegral_spectralGen_ℚ prime_fiveHundredSixtyThree

theorem isIntegral_and_degree_fiveHundredSixtyThree :
    IsIntegral ℤ (spectralGen 563) ∧
      (minpoly ℚ (spectralGen 563)).natDegree = 281 :=
  ⟨isIntegral_spectralGen_fiveHundredSixtyThree, degree_fiveHundredSixtyThree⟩

theorem fiveHundredSixtyThree_pack :
    IsIntegral ℤ (spectralGen 563) ∧
      (minpoly ℚ (spectralGen 563)).natDegree = 281 :=
  isIntegral_and_degree_fiveHundredSixtyThree

end Brockian.CosTraceNormFiveHundredSixtyThree
