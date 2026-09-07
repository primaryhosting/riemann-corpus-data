/-
  Brockian/CosTraceNormThreeHundredFiftyThree.lean — spectral generator at p = 353.

  [ℚ(2 cos 2π/353):ℚ] = 176 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormThreeHundredFiftyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_threeHundredFiftyThree : Nat.Prime 353 := by decide

theorem threeHundredFiftyThree_ne_two : (353 : ℕ) ≠ 2 := by decide

theorem degree_threeHundredFiftyThree : (minpoly ℚ (spectralGen 353)).natDegree = 176 :=
  real_subfield_degree prime_threeHundredFiftyThree threeHundredFiftyThree_ne_two

theorem isIntegral_spectralGen_threeHundredFiftyThree : IsIntegral ℤ (spectralGen 353) :=
  isIntegral_spectralGen prime_threeHundredFiftyThree

theorem isIntegral_spectralGen_threeHundredFiftyThree_Q : IsIntegral ℚ (spectralGen 353) :=
  isIntegral_spectralGen_ℚ prime_threeHundredFiftyThree

theorem isIntegral_and_degree_threeHundredFiftyThree :
    IsIntegral ℤ (spectralGen 353) ∧
      (minpoly ℚ (spectralGen 353)).natDegree = 176 :=
  ⟨isIntegral_spectralGen_threeHundredFiftyThree, degree_threeHundredFiftyThree⟩

theorem threeHundredFiftyThree_pack :
    IsIntegral ℤ (spectralGen 353) ∧
      (minpoly ℚ (spectralGen 353)).natDegree = 176 :=
  isIntegral_and_degree_threeHundredFiftyThree

end Brockian.CosTraceNormThreeHundredFiftyThree
