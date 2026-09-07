/-
  Brockian/CosTraceNormSixHundredFortyThree.lean — spectral generator at p = 643.

  [ℚ(2 cos 2π/643):ℚ] = 321 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSixHundredFortyThree

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sixHundredFortyThree : Nat.Prime 643 := by decide

theorem sixHundredFortyThree_ne_two : (643 : ℕ) ≠ 2 := by decide

theorem degree_sixHundredFortyThree : (minpoly ℚ (spectralGen 643)).natDegree = 321 :=
  real_subfield_degree prime_sixHundredFortyThree sixHundredFortyThree_ne_two

theorem isIntegral_spectralGen_sixHundredFortyThree : IsIntegral ℤ (spectralGen 643) :=
  isIntegral_spectralGen prime_sixHundredFortyThree

theorem isIntegral_spectralGen_sixHundredFortyThree_Q : IsIntegral ℚ (spectralGen 643) :=
  isIntegral_spectralGen_ℚ prime_sixHundredFortyThree

theorem isIntegral_and_degree_sixHundredFortyThree :
    IsIntegral ℤ (spectralGen 643) ∧
      (minpoly ℚ (spectralGen 643)).natDegree = 321 :=
  ⟨isIntegral_spectralGen_sixHundredFortyThree, degree_sixHundredFortyThree⟩

theorem sixHundredFortyThree_pack :
    IsIntegral ℤ (spectralGen 643) ∧
      (minpoly ℚ (spectralGen 643)).natDegree = 321 :=
  isIntegral_and_degree_sixHundredFortyThree

end Brockian.CosTraceNormSixHundredFortyThree
