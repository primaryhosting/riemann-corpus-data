/-
  Brockian/CosTraceNormSevenHundredSixtyNine.lean — spectral generator at p = 769.

  [ℚ(2 cos 2π/769):ℚ] = 384 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormSevenHundredSixtyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sevenHundredSixtyNine : Nat.Prime 769 := by decide

theorem sevenHundredSixtyNine_ne_two : (769 : ℕ) ≠ 2 := by decide

theorem degree_sevenHundredSixtyNine : (minpoly ℚ (spectralGen 769)).natDegree = 384 :=
  real_subfield_degree prime_sevenHundredSixtyNine sevenHundredSixtyNine_ne_two

theorem isIntegral_spectralGen_sevenHundredSixtyNine : IsIntegral ℤ (spectralGen 769) :=
  isIntegral_spectralGen prime_sevenHundredSixtyNine

theorem isIntegral_spectralGen_sevenHundredSixtyNine_Q : IsIntegral ℚ (spectralGen 769) :=
  isIntegral_spectralGen_ℚ prime_sevenHundredSixtyNine

theorem isIntegral_and_degree_sevenHundredSixtyNine :
    IsIntegral ℤ (spectralGen 769) ∧
      (minpoly ℚ (spectralGen 769)).natDegree = 384 :=
  ⟨isIntegral_spectralGen_sevenHundredSixtyNine, degree_sevenHundredSixtyNine⟩

theorem sevenHundredSixtyNine_pack :
    IsIntegral ℤ (spectralGen 769) ∧
      (minpoly ℚ (spectralGen 769)).natDegree = 384 :=
  isIntegral_and_degree_sevenHundredSixtyNine

end Brockian.CosTraceNormSevenHundredSixtyNine
