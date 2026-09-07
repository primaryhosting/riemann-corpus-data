/-
  Brockian/CosTraceNormTwoHundredThirtyNine.lean — spectral generator at p = 239.

  [ℚ(2 cos 2π/239):ℚ] = 119 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormTwoHundredThirtyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_twoHundredThirtyNine : Nat.Prime 239 := by decide

theorem twoHundredThirtyNine_ne_two : (239 : ℕ) ≠ 2 := by decide

theorem degree_twoHundredThirtyNine : (minpoly ℚ (spectralGen 239)).natDegree = 119 :=
  real_subfield_degree prime_twoHundredThirtyNine twoHundredThirtyNine_ne_two

theorem isIntegral_spectralGen_twoHundredThirtyNine : IsIntegral ℤ (spectralGen 239) :=
  isIntegral_spectralGen prime_twoHundredThirtyNine

theorem isIntegral_spectralGen_twoHundredThirtyNine_Q : IsIntegral ℚ (spectralGen 239) :=
  isIntegral_spectralGen_ℚ prime_twoHundredThirtyNine

theorem isIntegral_and_degree_twoHundredThirtyNine :
    IsIntegral ℤ (spectralGen 239) ∧
      (minpoly ℚ (spectralGen 239)).natDegree = 119 :=
  ⟨isIntegral_spectralGen_twoHundredThirtyNine, degree_twoHundredThirtyNine⟩

theorem twoHundredThirtyNine_pack :
    IsIntegral ℤ (spectralGen 239) ∧
      (minpoly ℚ (spectralGen 239)).natDegree = 119 :=
  isIntegral_and_degree_twoHundredThirtyNine

end Brockian.CosTraceNormTwoHundredThirtyNine
