/-
  Brockian/CosTraceNormFourHundredThirtyNine.lean — spectral generator at p = 439.

  [ℚ(2 cos 2π/439):ℚ] = 219 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFourHundredThirtyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fourHundredThirtyNine : Nat.Prime 439 := by decide

theorem fourHundredThirtyNine_ne_two : (439 : ℕ) ≠ 2 := by decide

theorem degree_fourHundredThirtyNine : (minpoly ℚ (spectralGen 439)).natDegree = 219 :=
  real_subfield_degree prime_fourHundredThirtyNine fourHundredThirtyNine_ne_two

theorem isIntegral_spectralGen_fourHundredThirtyNine : IsIntegral ℤ (spectralGen 439) :=
  isIntegral_spectralGen prime_fourHundredThirtyNine

theorem isIntegral_spectralGen_fourHundredThirtyNine_Q : IsIntegral ℚ (spectralGen 439) :=
  isIntegral_spectralGen_ℚ prime_fourHundredThirtyNine

theorem isIntegral_and_degree_fourHundredThirtyNine :
    IsIntegral ℤ (spectralGen 439) ∧
      (minpoly ℚ (spectralGen 439)).natDegree = 219 :=
  ⟨isIntegral_spectralGen_fourHundredThirtyNine, degree_fourHundredThirtyNine⟩

theorem fourHundredThirtyNine_pack :
    IsIntegral ℤ (spectralGen 439) ∧
      (minpoly ℚ (spectralGen 439)).natDegree = 219 :=
  isIntegral_and_degree_fourHundredThirtyNine

end Brockian.CosTraceNormFourHundredThirtyNine
