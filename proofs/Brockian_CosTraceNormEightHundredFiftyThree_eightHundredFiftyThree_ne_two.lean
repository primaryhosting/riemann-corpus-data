/-
  Brockian/CosTraceNormEightHundredFiftyThree.lean — spectral generator at p = 853.

  [ℚ(2 cos 2π/853):ℚ] = 426 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormEightHundredFiftyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_eightHundredFiftyThree : Nat.Prime 853 := by decide

theorem eightHundredFiftyThree_ne_two : (853 : ℕ) ≠ 2 := by decide

theorem degree_eightHundredFiftyThree : (minpoly ℚ (spectralGen 853)).natDegree = 426 :=
  real_subfield_degree prime_eightHundredFiftyThree eightHundredFiftyThree_ne_two

theorem isIntegral_spectralGen_eightHundredFiftyThree : IsIntegral ℤ (spectralGen 853) :=
  isIntegral_spectralGen prime_eightHundredFiftyThree

theorem isIntegral_spectralGen_eightHundredFiftyThree_Q : IsIntegral ℚ (spectralGen 853) :=
  isIntegral_spectralGen_ℚ prime_eightHundredFiftyThree

theorem isIntegral_and_degree_eightHundredFiftyThree :
    IsIntegral ℤ (spectralGen 853) ∧
      (minpoly ℚ (spectralGen 853)).natDegree = 426 :=
  ⟨isIntegral_spectralGen_eightHundredFiftyThree, degree_eightHundredFiftyThree⟩

theorem eightHundredFiftyThree_pack :
    IsIntegral ℤ (spectralGen 853) ∧
      (minpoly ℚ (spectralGen 853)).natDegree = 426 :=
  isIntegral_and_degree_eightHundredFiftyThree

end Brockian.CosTraceNormEightHundredFiftyThree
