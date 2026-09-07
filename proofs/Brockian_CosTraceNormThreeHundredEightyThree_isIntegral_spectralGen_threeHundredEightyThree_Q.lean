/-
  Brockian/CosTraceNormThreeHundredEightyThree.lean — spectral generator at p = 383.

  [ℚ(2 cos 2π/383):ℚ] = 191 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormThreeHundredEightyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_threeHundredEightyThree : Nat.Prime 383 := by decide

theorem threeHundredEightyThree_ne_two : (383 : ℕ) ≠ 2 := by decide

theorem degree_threeHundredEightyThree : (minpoly ℚ (spectralGen 383)).natDegree = 191 :=
  real_subfield_degree prime_threeHundredEightyThree threeHundredEightyThree_ne_two

theorem isIntegral_spectralGen_threeHundredEightyThree : IsIntegral ℤ (spectralGen 383) :=
  isIntegral_spectralGen prime_threeHundredEightyThree

theorem isIntegral_spectralGen_threeHundredEightyThree_Q : IsIntegral ℚ (spectralGen 383) :=
  isIntegral_spectralGen_ℚ prime_threeHundredEightyThree

theorem isIntegral_and_degree_threeHundredEightyThree :
    IsIntegral ℤ (spectralGen 383) ∧
      (minpoly ℚ (spectralGen 383)).natDegree = 191 :=
  ⟨isIntegral_spectralGen_threeHundredEightyThree, degree_threeHundredEightyThree⟩

theorem threeHundredEightyThree_pack :
    IsIntegral ℤ (spectralGen 383) ∧
      (minpoly ℚ (spectralGen 383)).natDegree = 191 :=
  isIntegral_and_degree_threeHundredEightyThree

end Brockian.CosTraceNormThreeHundredEightyThree
