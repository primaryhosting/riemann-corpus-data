/-
  Brockian/CosTraceNormFiveHundredNine.lean — spectral generator at p = 509.

  [ℚ(2 cos 2π/509):ℚ] = 254 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormFiveHundredNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fiveHundredNine : Nat.Prime 509 := by decide

theorem fiveHundredNine_ne_two : (509 : ℕ) ≠ 2 := by decide

theorem degree_fiveHundredNine : (minpoly ℚ (spectralGen 509)).natDegree = 254 :=
  real_subfield_degree prime_fiveHundredNine fiveHundredNine_ne_two

theorem isIntegral_spectralGen_fiveHundredNine : IsIntegral ℤ (spectralGen 509) :=
  isIntegral_spectralGen prime_fiveHundredNine

theorem isIntegral_spectralGen_fiveHundredNine_Q : IsIntegral ℚ (spectralGen 509) :=
  isIntegral_spectralGen_ℚ prime_fiveHundredNine

theorem isIntegral_and_degree_fiveHundredNine :
    IsIntegral ℤ (spectralGen 509) ∧
      (minpoly ℚ (spectralGen 509)).natDegree = 254 :=
  ⟨isIntegral_spectralGen_fiveHundredNine, degree_fiveHundredNine⟩

theorem fiveHundredNine_pack :
    IsIntegral ℤ (spectralGen 509) ∧
      (minpoly ℚ (spectralGen 509)).natDegree = 254 :=
  isIntegral_and_degree_fiveHundredNine

end Brockian.CosTraceNormFiveHundredNine
