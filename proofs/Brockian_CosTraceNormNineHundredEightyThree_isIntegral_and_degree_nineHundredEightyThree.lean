/-
  Brockian/CosTraceNormNineHundredEightyThree.lean — spectral generator at p = 983.

  [ℚ(2 cos 2π/983):ℚ] = 491 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormNineHundredEightyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_nineHundredEightyThree : Nat.Prime 983 := by decide

theorem nineHundredEightyThree_ne_two : (983 : ℕ) ≠ 2 := by decide

theorem degree_nineHundredEightyThree : (minpoly ℚ (spectralGen 983)).natDegree = 491 :=
  real_subfield_degree prime_nineHundredEightyThree nineHundredEightyThree_ne_two

theorem isIntegral_spectralGen_nineHundredEightyThree : IsIntegral ℤ (spectralGen 983) :=
  isIntegral_spectralGen prime_nineHundredEightyThree

theorem isIntegral_spectralGen_nineHundredEightyThree_Q : IsIntegral ℚ (spectralGen 983) :=
  isIntegral_spectralGen_ℚ prime_nineHundredEightyThree

theorem isIntegral_and_degree_nineHundredEightyThree :
    IsIntegral ℤ (spectralGen 983) ∧
      (minpoly ℚ (spectralGen 983)).natDegree = 491 :=
  ⟨isIntegral_spectralGen_nineHundredEightyThree, degree_nineHundredEightyThree⟩

theorem nineHundredEightyThree_pack :
    IsIntegral ℤ (spectralGen 983) ∧
      (minpoly ℚ (spectralGen 983)).natDegree = 491 :=
  isIntegral_and_degree_nineHundredEightyThree

end Brockian.CosTraceNormNineHundredEightyThree
