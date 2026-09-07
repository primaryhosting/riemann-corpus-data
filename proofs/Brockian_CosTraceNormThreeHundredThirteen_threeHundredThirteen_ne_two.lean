/-
  Brockian/CosTraceNormThreeHundredThirteen.lean — spectral generator at p = 313.

  [ℚ(2 cos 2π/313):ℚ] = 156 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormThreeHundredThirteen

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_threeHundredThirteen : Nat.Prime 313 := by decide

theorem threeHundredThirteen_ne_two : (313 : ℕ) ≠ 2 := by decide

theorem degree_threeHundredThirteen : (minpoly ℚ (spectralGen 313)).natDegree = 156 :=
  real_subfield_degree prime_threeHundredThirteen threeHundredThirteen_ne_two

theorem isIntegral_spectralGen_threeHundredThirteen : IsIntegral ℤ (spectralGen 313) :=
  isIntegral_spectralGen prime_threeHundredThirteen

theorem isIntegral_spectralGen_threeHundredThirteen_Q : IsIntegral ℚ (spectralGen 313) :=
  isIntegral_spectralGen_ℚ prime_threeHundredThirteen

theorem isIntegral_and_degree_threeHundredThirteen :
    IsIntegral ℤ (spectralGen 313) ∧
      (minpoly ℚ (spectralGen 313)).natDegree = 156 :=
  ⟨isIntegral_spectralGen_threeHundredThirteen, degree_threeHundredThirteen⟩

theorem threeHundredThirteen_pack :
    IsIntegral ℤ (spectralGen 313) ∧
      (minpoly ℚ (spectralGen 313)).natDegree = 156 :=
  isIntegral_and_degree_threeHundredThirteen

end Brockian.CosTraceNormThreeHundredThirteen
