/-
  Brockian/CosTraceNormSixHundredEightyThree.lean — spectral generator at p = 683.

  [ℚ(2 cos 2π/683):ℚ] = 341 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSixHundredEightyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sixHundredEightyThree : Nat.Prime 683 := by decide

theorem sixHundredEightyThree_ne_two : (683 : ℕ) ≠ 2 := by decide

theorem degree_sixHundredEightyThree : (minpoly ℚ (spectralGen 683)).natDegree = 341 :=
  real_subfield_degree prime_sixHundredEightyThree sixHundredEightyThree_ne_two

theorem isIntegral_spectralGen_sixHundredEightyThree : IsIntegral ℤ (spectralGen 683) :=
  isIntegral_spectralGen prime_sixHundredEightyThree

theorem isIntegral_spectralGen_sixHundredEightyThree_Q : IsIntegral ℚ (spectralGen 683) :=
  isIntegral_spectralGen_ℚ prime_sixHundredEightyThree

theorem isIntegral_and_degree_sixHundredEightyThree :
    IsIntegral ℤ (spectralGen 683) ∧
      (minpoly ℚ (spectralGen 683)).natDegree = 341 :=
  ⟨isIntegral_spectralGen_sixHundredEightyThree, degree_sixHundredEightyThree⟩

theorem sixHundredEightyThree_pack :
    IsIntegral ℤ (spectralGen 683) ∧
      (minpoly ℚ (spectralGen 683)).natDegree = 341 :=
  isIntegral_and_degree_sixHundredEightyThree

end Brockian.CosTraceNormSixHundredEightyThree
