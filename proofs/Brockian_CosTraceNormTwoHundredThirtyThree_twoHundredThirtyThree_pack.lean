/-
  Brockian/CosTraceNormTwoHundredThirtyThree.lean — spectral generator at p = 233.

  [ℚ(2 cos 2π/233):ℚ] = 116 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormTwoHundredThirtyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_twoHundredThirtyThree : Nat.Prime 233 := by decide

theorem twoHundredThirtyThree_ne_two : (233 : ℕ) ≠ 2 := by decide

theorem degree_twoHundredThirtyThree : (minpoly ℚ (spectralGen 233)).natDegree = 116 :=
  real_subfield_degree prime_twoHundredThirtyThree twoHundredThirtyThree_ne_two

theorem isIntegral_spectralGen_twoHundredThirtyThree : IsIntegral ℤ (spectralGen 233) :=
  isIntegral_spectralGen prime_twoHundredThirtyThree

theorem isIntegral_spectralGen_twoHundredThirtyThree_Q : IsIntegral ℚ (spectralGen 233) :=
  isIntegral_spectralGen_ℚ prime_twoHundredThirtyThree

theorem isIntegral_and_degree_twoHundredThirtyThree :
    IsIntegral ℤ (spectralGen 233) ∧
      (minpoly ℚ (spectralGen 233)).natDegree = 116 :=
  ⟨isIntegral_spectralGen_twoHundredThirtyThree, degree_twoHundredThirtyThree⟩

theorem twoHundredThirtyThree_pack :
    IsIntegral ℤ (spectralGen 233) ∧
      (minpoly ℚ (spectralGen 233)).natDegree = 116 :=
  isIntegral_and_degree_twoHundredThirtyThree

end Brockian.CosTraceNormTwoHundredThirtyThree
