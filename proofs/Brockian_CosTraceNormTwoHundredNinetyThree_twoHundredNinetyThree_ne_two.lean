/-
  Brockian/CosTraceNormTwoHundredNinetyThree.lean — spectral generator at p = 293.

  [ℚ(2 cos 2π/293):ℚ] = 146 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormTwoHundredNinetyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_twoHundredNinetyThree : Nat.Prime 293 := by decide

theorem twoHundredNinetyThree_ne_two : (293 : ℕ) ≠ 2 := by decide

theorem degree_twoHundredNinetyThree : (minpoly ℚ (spectralGen 293)).natDegree = 146 :=
  real_subfield_degree prime_twoHundredNinetyThree twoHundredNinetyThree_ne_two

theorem isIntegral_spectralGen_twoHundredNinetyThree : IsIntegral ℤ (spectralGen 293) :=
  isIntegral_spectralGen prime_twoHundredNinetyThree

theorem isIntegral_spectralGen_twoHundredNinetyThree_Q : IsIntegral ℚ (spectralGen 293) :=
  isIntegral_spectralGen_ℚ prime_twoHundredNinetyThree

theorem isIntegral_and_degree_twoHundredNinetyThree :
    IsIntegral ℤ (spectralGen 293) ∧
      (minpoly ℚ (spectralGen 293)).natDegree = 146 :=
  ⟨isIntegral_spectralGen_twoHundredNinetyThree, degree_twoHundredNinetyThree⟩

theorem twoHundredNinetyThree_pack :
    IsIntegral ℤ (spectralGen 293) ∧
      (minpoly ℚ (spectralGen 293)).natDegree = 146 :=
  isIntegral_and_degree_twoHundredNinetyThree

end Brockian.CosTraceNormTwoHundredNinetyThree
