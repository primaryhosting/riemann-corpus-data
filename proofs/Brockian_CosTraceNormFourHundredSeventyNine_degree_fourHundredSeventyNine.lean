/-
  Brockian/CosTraceNormFourHundredSeventyNine.lean — spectral generator at p = 479.

  [ℚ(2 cos 2π/479):ℚ] = 239 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFourHundredSeventyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fourHundredSeventyNine : Nat.Prime 479 := by decide

theorem fourHundredSeventyNine_ne_two : (479 : ℕ) ≠ 2 := by decide

theorem degree_fourHundredSeventyNine : (minpoly ℚ (spectralGen 479)).natDegree = 239 :=
  real_subfield_degree prime_fourHundredSeventyNine fourHundredSeventyNine_ne_two

theorem isIntegral_spectralGen_fourHundredSeventyNine : IsIntegral ℤ (spectralGen 479) :=
  isIntegral_spectralGen prime_fourHundredSeventyNine

theorem isIntegral_spectralGen_fourHundredSeventyNine_Q : IsIntegral ℚ (spectralGen 479) :=
  isIntegral_spectralGen_ℚ prime_fourHundredSeventyNine

theorem isIntegral_and_degree_fourHundredSeventyNine :
    IsIntegral ℤ (spectralGen 479) ∧
      (minpoly ℚ (spectralGen 479)).natDegree = 239 :=
  ⟨isIntegral_spectralGen_fourHundredSeventyNine, degree_fourHundredSeventyNine⟩

theorem fourHundredSeventyNine_pack :
    IsIntegral ℤ (spectralGen 479) ∧
      (minpoly ℚ (spectralGen 479)).natDegree = 239 :=
  isIntegral_and_degree_fourHundredSeventyNine

end Brockian.CosTraceNormFourHundredSeventyNine
