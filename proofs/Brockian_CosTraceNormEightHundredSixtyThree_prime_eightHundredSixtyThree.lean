/-
  Brockian/CosTraceNormEightHundredSixtyThree.lean — spectral generator at p = 863.

  [ℚ(2 cos 2π/863):ℚ] = 431 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormEightHundredSixtyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_eightHundredSixtyThree : Nat.Prime 863 := by decide

theorem eightHundredSixtyThree_ne_two : (863 : ℕ) ≠ 2 := by decide

theorem degree_eightHundredSixtyThree : (minpoly ℚ (spectralGen 863)).natDegree = 431 :=
  real_subfield_degree prime_eightHundredSixtyThree eightHundredSixtyThree_ne_two

theorem isIntegral_spectralGen_eightHundredSixtyThree : IsIntegral ℤ (spectralGen 863) :=
  isIntegral_spectralGen prime_eightHundredSixtyThree

theorem isIntegral_spectralGen_eightHundredSixtyThree_Q : IsIntegral ℚ (spectralGen 863) :=
  isIntegral_spectralGen_ℚ prime_eightHundredSixtyThree

theorem isIntegral_and_degree_eightHundredSixtyThree :
    IsIntegral ℤ (spectralGen 863) ∧
      (minpoly ℚ (spectralGen 863)).natDegree = 431 :=
  ⟨isIntegral_spectralGen_eightHundredSixtyThree, degree_eightHundredSixtyThree⟩

theorem eightHundredSixtyThree_pack :
    IsIntegral ℤ (spectralGen 863) ∧
      (minpoly ℚ (spectralGen 863)).natDegree = 431 :=
  isIntegral_and_degree_eightHundredSixtyThree

end Brockian.CosTraceNormEightHundredSixtyThree
