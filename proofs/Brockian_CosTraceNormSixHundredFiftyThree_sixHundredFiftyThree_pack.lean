/-
  Brockian/CosTraceNormSixHundredFiftyThree.lean — spectral generator at p = 653.

  [ℚ(2 cos 2π/653):ℚ] = 326 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSixHundredFiftyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sixHundredFiftyThree : Nat.Prime 653 := by decide

theorem sixHundredFiftyThree_ne_two : (653 : ℕ) ≠ 2 := by decide

theorem degree_sixHundredFiftyThree : (minpoly ℚ (spectralGen 653)).natDegree = 326 :=
  real_subfield_degree prime_sixHundredFiftyThree sixHundredFiftyThree_ne_two

theorem isIntegral_spectralGen_sixHundredFiftyThree : IsIntegral ℤ (spectralGen 653) :=
  isIntegral_spectralGen prime_sixHundredFiftyThree

theorem isIntegral_spectralGen_sixHundredFiftyThree_Q : IsIntegral ℚ (spectralGen 653) :=
  isIntegral_spectralGen_ℚ prime_sixHundredFiftyThree

theorem isIntegral_and_degree_sixHundredFiftyThree :
    IsIntegral ℤ (spectralGen 653) ∧
      (minpoly ℚ (spectralGen 653)).natDegree = 326 :=
  ⟨isIntegral_spectralGen_sixHundredFiftyThree, degree_sixHundredFiftyThree⟩

theorem sixHundredFiftyThree_pack :
    IsIntegral ℤ (spectralGen 653) ∧
      (minpoly ℚ (spectralGen 653)).natDegree = 326 :=
  isIntegral_and_degree_sixHundredFiftyThree

end Brockian.CosTraceNormSixHundredFiftyThree
