/-
  Brockian/CosTraceNormTwoHundredTwentyNine.lean — spectral generator at p = 229.

  [ℚ(2 cos 2π/229):ℚ] = 114 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormTwoHundredTwentyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_twoHundredTwentyNine : Nat.Prime 229 := by decide

theorem twoHundredTwentyNine_ne_two : (229 : ℕ) ≠ 2 := by decide

theorem degree_twoHundredTwentyNine : (minpoly ℚ (spectralGen 229)).natDegree = 114 :=
  real_subfield_degree prime_twoHundredTwentyNine twoHundredTwentyNine_ne_two

theorem isIntegral_spectralGen_twoHundredTwentyNine : IsIntegral ℤ (spectralGen 229) :=
  isIntegral_spectralGen prime_twoHundredTwentyNine

theorem isIntegral_spectralGen_twoHundredTwentyNine_Q : IsIntegral ℚ (spectralGen 229) :=
  isIntegral_spectralGen_ℚ prime_twoHundredTwentyNine

theorem isIntegral_and_degree_twoHundredTwentyNine :
    IsIntegral ℤ (spectralGen 229) ∧
      (minpoly ℚ (spectralGen 229)).natDegree = 114 :=
  ⟨isIntegral_spectralGen_twoHundredTwentyNine, degree_twoHundredTwentyNine⟩

theorem twoHundredTwentyNine_pack :
    IsIntegral ℤ (spectralGen 229) ∧
      (minpoly ℚ (spectralGen 229)).natDegree = 114 :=
  isIntegral_and_degree_twoHundredTwentyNine

end Brockian.CosTraceNormTwoHundredTwentyNine
