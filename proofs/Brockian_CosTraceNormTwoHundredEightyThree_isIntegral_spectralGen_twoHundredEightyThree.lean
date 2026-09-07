/-
  Brockian/CosTraceNormTwoHundredEightyThree.lean — spectral generator at p = 283.

  [ℚ(2 cos 2π/283):ℚ] = 141 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormTwoHundredEightyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_twoHundredEightyThree : Nat.Prime 283 := by decide

theorem twoHundredEightyThree_ne_two : (283 : ℕ) ≠ 2 := by decide

theorem degree_twoHundredEightyThree : (minpoly ℚ (spectralGen 283)).natDegree = 141 :=
  real_subfield_degree prime_twoHundredEightyThree twoHundredEightyThree_ne_two

theorem isIntegral_spectralGen_twoHundredEightyThree : IsIntegral ℤ (spectralGen 283) :=
  isIntegral_spectralGen prime_twoHundredEightyThree

theorem isIntegral_spectralGen_twoHundredEightyThree_Q : IsIntegral ℚ (spectralGen 283) :=
  isIntegral_spectralGen_ℚ prime_twoHundredEightyThree

theorem isIntegral_and_degree_twoHundredEightyThree :
    IsIntegral ℤ (spectralGen 283) ∧
      (minpoly ℚ (spectralGen 283)).natDegree = 141 :=
  ⟨isIntegral_spectralGen_twoHundredEightyThree, degree_twoHundredEightyThree⟩

theorem twoHundredEightyThree_pack :
    IsIntegral ℤ (spectralGen 283) ∧
      (minpoly ℚ (spectralGen 283)).natDegree = 141 :=
  isIntegral_and_degree_twoHundredEightyThree

end Brockian.CosTraceNormTwoHundredEightyThree
