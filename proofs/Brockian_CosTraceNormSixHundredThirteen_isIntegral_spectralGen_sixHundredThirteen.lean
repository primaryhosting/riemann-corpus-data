/-
  Brockian/CosTraceNormSixHundredThirteen.lean — spectral generator at p = 613.

  [ℚ(2 cos 2π/613):ℚ] = 306 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSixHundredThirteen

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sixHundredThirteen : Nat.Prime 613 := by decide

theorem sixHundredThirteen_ne_two : (613 : ℕ) ≠ 2 := by decide

theorem degree_sixHundredThirteen : (minpoly ℚ (spectralGen 613)).natDegree = 306 :=
  real_subfield_degree prime_sixHundredThirteen sixHundredThirteen_ne_two

theorem isIntegral_spectralGen_sixHundredThirteen : IsIntegral ℤ (spectralGen 613) :=
  isIntegral_spectralGen prime_sixHundredThirteen

theorem isIntegral_spectralGen_sixHundredThirteen_Q : IsIntegral ℚ (spectralGen 613) :=
  isIntegral_spectralGen_ℚ prime_sixHundredThirteen

theorem isIntegral_and_degree_sixHundredThirteen :
    IsIntegral ℤ (spectralGen 613) ∧
      (minpoly ℚ (spectralGen 613)).natDegree = 306 :=
  ⟨isIntegral_spectralGen_sixHundredThirteen, degree_sixHundredThirteen⟩

theorem sixHundredThirteen_pack :
    IsIntegral ℤ (spectralGen 613) ∧
      (minpoly ℚ (spectralGen 613)).natDegree = 306 :=
  isIntegral_and_degree_sixHundredThirteen

end Brockian.CosTraceNormSixHundredThirteen
