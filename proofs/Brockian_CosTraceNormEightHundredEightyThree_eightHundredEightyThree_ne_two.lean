/-
  Brockian/CosTraceNormEightHundredEightyThree.lean — spectral generator at p = 883.

  [ℚ(2 cos 2π/883):ℚ] = 441 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormEightHundredEightyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_eightHundredEightyThree : Nat.Prime 883 := by decide

theorem eightHundredEightyThree_ne_two : (883 : ℕ) ≠ 2 := by decide

theorem degree_eightHundredEightyThree : (minpoly ℚ (spectralGen 883)).natDegree = 441 :=
  real_subfield_degree prime_eightHundredEightyThree eightHundredEightyThree_ne_two

theorem isIntegral_spectralGen_eightHundredEightyThree : IsIntegral ℤ (spectralGen 883) :=
  isIntegral_spectralGen prime_eightHundredEightyThree

theorem isIntegral_spectralGen_eightHundredEightyThree_Q : IsIntegral ℚ (spectralGen 883) :=
  isIntegral_spectralGen_ℚ prime_eightHundredEightyThree

theorem isIntegral_and_degree_eightHundredEightyThree :
    IsIntegral ℤ (spectralGen 883) ∧
      (minpoly ℚ (spectralGen 883)).natDegree = 441 :=
  ⟨isIntegral_spectralGen_eightHundredEightyThree, degree_eightHundredEightyThree⟩

theorem eightHundredEightyThree_pack :
    IsIntegral ℤ (spectralGen 883) ∧
      (minpoly ℚ (spectralGen 883)).natDegree = 441 :=
  isIntegral_and_degree_eightHundredEightyThree

end Brockian.CosTraceNormEightHundredEightyThree
