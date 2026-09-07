/-
  Brockian/CosTraceNormFourHundredThirtyThree.lean — spectral generator at p = 433.

  [ℚ(2 cos 2π/433):ℚ] = 216 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFourHundredThirtyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fourHundredThirtyThree : Nat.Prime 433 := by decide

theorem fourHundredThirtyThree_ne_two : (433 : ℕ) ≠ 2 := by decide

theorem degree_fourHundredThirtyThree : (minpoly ℚ (spectralGen 433)).natDegree = 216 :=
  real_subfield_degree prime_fourHundredThirtyThree fourHundredThirtyThree_ne_two

theorem isIntegral_spectralGen_fourHundredThirtyThree : IsIntegral ℤ (spectralGen 433) :=
  isIntegral_spectralGen prime_fourHundredThirtyThree

theorem isIntegral_spectralGen_fourHundredThirtyThree_Q : IsIntegral ℚ (spectralGen 433) :=
  isIntegral_spectralGen_ℚ prime_fourHundredThirtyThree

theorem isIntegral_and_degree_fourHundredThirtyThree :
    IsIntegral ℤ (spectralGen 433) ∧
      (minpoly ℚ (spectralGen 433)).natDegree = 216 :=
  ⟨isIntegral_spectralGen_fourHundredThirtyThree, degree_fourHundredThirtyThree⟩

theorem fourHundredThirtyThree_pack :
    IsIntegral ℤ (spectralGen 433) ∧
      (minpoly ℚ (spectralGen 433)).natDegree = 216 :=
  isIntegral_and_degree_fourHundredThirtyThree

end Brockian.CosTraceNormFourHundredThirtyThree
