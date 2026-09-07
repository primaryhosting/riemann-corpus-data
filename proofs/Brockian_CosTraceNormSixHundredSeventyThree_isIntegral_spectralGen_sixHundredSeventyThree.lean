/-
  Brockian/CosTraceNormSixHundredSeventyThree.lean — spectral generator at p = 673.

  [ℚ(2 cos 2π/673):ℚ] = 336 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSixHundredSeventyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sixHundredSeventyThree : Nat.Prime 673 := by decide

theorem sixHundredSeventyThree_ne_two : (673 : ℕ) ≠ 2 := by decide

theorem degree_sixHundredSeventyThree : (minpoly ℚ (spectralGen 673)).natDegree = 336 :=
  real_subfield_degree prime_sixHundredSeventyThree sixHundredSeventyThree_ne_two

theorem isIntegral_spectralGen_sixHundredSeventyThree : IsIntegral ℤ (spectralGen 673) :=
  isIntegral_spectralGen prime_sixHundredSeventyThree

theorem isIntegral_spectralGen_sixHundredSeventyThree_Q : IsIntegral ℚ (spectralGen 673) :=
  isIntegral_spectralGen_ℚ prime_sixHundredSeventyThree

theorem isIntegral_and_degree_sixHundredSeventyThree :
    IsIntegral ℤ (spectralGen 673) ∧
      (minpoly ℚ (spectralGen 673)).natDegree = 336 :=
  ⟨isIntegral_spectralGen_sixHundredSeventyThree, degree_sixHundredSeventyThree⟩

theorem sixHundredSeventyThree_pack :
    IsIntegral ℤ (spectralGen 673) ∧
      (minpoly ℚ (spectralGen 673)).natDegree = 336 :=
  isIntegral_and_degree_sixHundredSeventyThree

end Brockian.CosTraceNormSixHundredSeventyThree
