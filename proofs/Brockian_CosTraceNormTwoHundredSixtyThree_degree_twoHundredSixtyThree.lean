/-
  Brockian/CosTraceNormTwoHundredSixtyThree.lean — spectral generator at p = 263.

  [ℚ(2 cos 2π/263):ℚ] = 131 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormTwoHundredSixtyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_twoHundredSixtyThree : Nat.Prime 263 := by decide

theorem twoHundredSixtyThree_ne_two : (263 : ℕ) ≠ 2 := by decide

theorem degree_twoHundredSixtyThree : (minpoly ℚ (spectralGen 263)).natDegree = 131 :=
  real_subfield_degree prime_twoHundredSixtyThree twoHundredSixtyThree_ne_two

theorem isIntegral_spectralGen_twoHundredSixtyThree : IsIntegral ℤ (spectralGen 263) :=
  isIntegral_spectralGen prime_twoHundredSixtyThree

theorem isIntegral_spectralGen_twoHundredSixtyThree_Q : IsIntegral ℚ (spectralGen 263) :=
  isIntegral_spectralGen_ℚ prime_twoHundredSixtyThree

theorem isIntegral_and_degree_twoHundredSixtyThree :
    IsIntegral ℤ (spectralGen 263) ∧
      (minpoly ℚ (spectralGen 263)).natDegree = 131 :=
  ⟨isIntegral_spectralGen_twoHundredSixtyThree, degree_twoHundredSixtyThree⟩

theorem twoHundredSixtyThree_pack :
    IsIntegral ℤ (spectralGen 263) ∧
      (minpoly ℚ (spectralGen 263)).natDegree = 131 :=
  isIntegral_and_degree_twoHundredSixtyThree

end Brockian.CosTraceNormTwoHundredSixtyThree
