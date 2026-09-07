/-
  Brockian/CosTraceNormThreeHundredSeventeen.lean — spectral generator at p = 317.

  [ℚ(2 cos 2π/317):ℚ] = 158 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormThreeHundredSeventeen

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_threeHundredSeventeen : Nat.Prime 317 := by decide

theorem threeHundredSeventeen_ne_two : (317 : ℕ) ≠ 2 := by decide

theorem degree_threeHundredSeventeen : (minpoly ℚ (spectralGen 317)).natDegree = 158 :=
  real_subfield_degree prime_threeHundredSeventeen threeHundredSeventeen_ne_two

theorem isIntegral_spectralGen_threeHundredSeventeen : IsIntegral ℤ (spectralGen 317) :=
  isIntegral_spectralGen prime_threeHundredSeventeen

theorem isIntegral_spectralGen_threeHundredSeventeen_Q : IsIntegral ℚ (spectralGen 317) :=
  isIntegral_spectralGen_ℚ prime_threeHundredSeventeen

theorem isIntegral_and_degree_threeHundredSeventeen :
    IsIntegral ℤ (spectralGen 317) ∧
      (minpoly ℚ (spectralGen 317)).natDegree = 158 :=
  ⟨isIntegral_spectralGen_threeHundredSeventeen, degree_threeHundredSeventeen⟩

theorem threeHundredSeventeen_pack :
    IsIntegral ℤ (spectralGen 317) ∧
      (minpoly ℚ (spectralGen 317)).natDegree = 158 :=
  isIntegral_and_degree_threeHundredSeventeen

end Brockian.CosTraceNormThreeHundredSeventeen
