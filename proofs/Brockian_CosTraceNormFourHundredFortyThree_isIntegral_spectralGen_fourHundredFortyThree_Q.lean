/-
  Brockian/CosTraceNormFourHundredFortyThree.lean — spectral generator at p = 443.

  [ℚ(2 cos 2π/443):ℚ] = 221 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFourHundredFortyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fourHundredFortyThree : Nat.Prime 443 := by decide

theorem fourHundredFortyThree_ne_two : (443 : ℕ) ≠ 2 := by decide

theorem degree_fourHundredFortyThree : (minpoly ℚ (spectralGen 443)).natDegree = 221 :=
  real_subfield_degree prime_fourHundredFortyThree fourHundredFortyThree_ne_two

theorem isIntegral_spectralGen_fourHundredFortyThree : IsIntegral ℤ (spectralGen 443) :=
  isIntegral_spectralGen prime_fourHundredFortyThree

theorem isIntegral_spectralGen_fourHundredFortyThree_Q : IsIntegral ℚ (spectralGen 443) :=
  isIntegral_spectralGen_ℚ prime_fourHundredFortyThree

theorem isIntegral_and_degree_fourHundredFortyThree :
    IsIntegral ℤ (spectralGen 443) ∧
      (minpoly ℚ (spectralGen 443)).natDegree = 221 :=
  ⟨isIntegral_spectralGen_fourHundredFortyThree, degree_fourHundredFortyThree⟩

theorem fourHundredFortyThree_pack :
    IsIntegral ℤ (spectralGen 443) ∧
      (minpoly ℚ (spectralGen 443)).natDegree = 221 :=
  isIntegral_and_degree_fourHundredFortyThree

end Brockian.CosTraceNormFourHundredFortyThree
