/-
  Brockian/CosTraceNormFourHundredSixtyThree.lean — spectral generator at p = 463.

  [ℚ(2 cos 2π/463):ℚ] = 231 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFourHundredSixtyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fourHundredSixtyThree : Nat.Prime 463 := by decide

theorem fourHundredSixtyThree_ne_two : (463 : ℕ) ≠ 2 := by decide

theorem degree_fourHundredSixtyThree : (minpoly ℚ (spectralGen 463)).natDegree = 231 :=
  real_subfield_degree prime_fourHundredSixtyThree fourHundredSixtyThree_ne_two

theorem isIntegral_spectralGen_fourHundredSixtyThree : IsIntegral ℤ (spectralGen 463) :=
  isIntegral_spectralGen prime_fourHundredSixtyThree

theorem isIntegral_spectralGen_fourHundredSixtyThree_Q : IsIntegral ℚ (spectralGen 463) :=
  isIntegral_spectralGen_ℚ prime_fourHundredSixtyThree

theorem isIntegral_and_degree_fourHundredSixtyThree :
    IsIntegral ℤ (spectralGen 463) ∧
      (minpoly ℚ (spectralGen 463)).natDegree = 231 :=
  ⟨isIntegral_spectralGen_fourHundredSixtyThree, degree_fourHundredSixtyThree⟩

theorem fourHundredSixtyThree_pack :
    IsIntegral ℤ (spectralGen 463) ∧
      (minpoly ℚ (spectralGen 463)).natDegree = 231 :=
  isIntegral_and_degree_fourHundredSixtyThree

end Brockian.CosTraceNormFourHundredSixtyThree
