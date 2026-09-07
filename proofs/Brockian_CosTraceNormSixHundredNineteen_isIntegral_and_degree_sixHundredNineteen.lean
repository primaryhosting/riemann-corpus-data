/-
  Brockian/CosTraceNormSixHundredNineteen.lean — spectral generator at p = 619.

  [ℚ(2 cos 2π/619):ℚ] = 309 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSixHundredNineteen

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sixHundredNineteen : Nat.Prime 619 := by decide

theorem sixHundredNineteen_ne_two : (619 : ℕ) ≠ 2 := by decide

theorem degree_sixHundredNineteen : (minpoly ℚ (spectralGen 619)).natDegree = 309 :=
  real_subfield_degree prime_sixHundredNineteen sixHundredNineteen_ne_two

theorem isIntegral_spectralGen_sixHundredNineteen : IsIntegral ℤ (spectralGen 619) :=
  isIntegral_spectralGen prime_sixHundredNineteen

theorem isIntegral_spectralGen_sixHundredNineteen_Q : IsIntegral ℚ (spectralGen 619) :=
  isIntegral_spectralGen_ℚ prime_sixHundredNineteen

theorem isIntegral_and_degree_sixHundredNineteen :
    IsIntegral ℤ (spectralGen 619) ∧
      (minpoly ℚ (spectralGen 619)).natDegree = 309 :=
  ⟨isIntegral_spectralGen_sixHundredNineteen, degree_sixHundredNineteen⟩

theorem sixHundredNineteen_pack :
    IsIntegral ℤ (spectralGen 619) ∧
      (minpoly ℚ (spectralGen 619)).natDegree = 309 :=
  isIntegral_and_degree_sixHundredNineteen

end Brockian.CosTraceNormSixHundredNineteen
