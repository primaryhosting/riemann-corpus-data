/-
  Brockian/CosTraceNormSixHundredSeventeen.lean — spectral generator at p = 617.

  [ℚ(2 cos 2π/617):ℚ] = 308 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSixHundredSeventeen

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sixHundredSeventeen : Nat.Prime 617 := by decide

theorem sixHundredSeventeen_ne_two : (617 : ℕ) ≠ 2 := by decide

theorem degree_sixHundredSeventeen : (minpoly ℚ (spectralGen 617)).natDegree = 308 :=
  real_subfield_degree prime_sixHundredSeventeen sixHundredSeventeen_ne_two

theorem isIntegral_spectralGen_sixHundredSeventeen : IsIntegral ℤ (spectralGen 617) :=
  isIntegral_spectralGen prime_sixHundredSeventeen

theorem isIntegral_spectralGen_sixHundredSeventeen_Q : IsIntegral ℚ (spectralGen 617) :=
  isIntegral_spectralGen_ℚ prime_sixHundredSeventeen

theorem isIntegral_and_degree_sixHundredSeventeen :
    IsIntegral ℤ (spectralGen 617) ∧
      (minpoly ℚ (spectralGen 617)).natDegree = 308 :=
  ⟨isIntegral_spectralGen_sixHundredSeventeen, degree_sixHundredSeventeen⟩

theorem sixHundredSeventeen_pack :
    IsIntegral ℤ (spectralGen 617) ∧
      (minpoly ℚ (spectralGen 617)).natDegree = 308 :=
  isIntegral_and_degree_sixHundredSeventeen

end Brockian.CosTraceNormSixHundredSeventeen
