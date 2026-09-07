/-
  Brockian/CosTraceNormSevenHundredSeventyThree.lean — spectral generator at p = 773.

  [ℚ(2 cos 2π/773):ℚ] = 386 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSevenHundredSeventyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sevenHundredSeventyThree : Nat.Prime 773 := by decide

theorem sevenHundredSeventyThree_ne_two : (773 : ℕ) ≠ 2 := by decide

theorem degree_sevenHundredSeventyThree : (minpoly ℚ (spectralGen 773)).natDegree = 386 :=
  real_subfield_degree prime_sevenHundredSeventyThree sevenHundredSeventyThree_ne_two

theorem isIntegral_spectralGen_sevenHundredSeventyThree : IsIntegral ℤ (spectralGen 773) :=
  isIntegral_spectralGen prime_sevenHundredSeventyThree

theorem isIntegral_spectralGen_sevenHundredSeventyThree_Q : IsIntegral ℚ (spectralGen 773) :=
  isIntegral_spectralGen_ℚ prime_sevenHundredSeventyThree

theorem isIntegral_and_degree_sevenHundredSeventyThree :
    IsIntegral ℤ (spectralGen 773) ∧
      (minpoly ℚ (spectralGen 773)).natDegree = 386 :=
  ⟨isIntegral_spectralGen_sevenHundredSeventyThree, degree_sevenHundredSeventyThree⟩

theorem sevenHundredSeventyThree_pack :
    IsIntegral ℤ (spectralGen 773) ∧
      (minpoly ℚ (spectralGen 773)).natDegree = 386 :=
  isIntegral_and_degree_sevenHundredSeventyThree

end Brockian.CosTraceNormSevenHundredSeventyThree
