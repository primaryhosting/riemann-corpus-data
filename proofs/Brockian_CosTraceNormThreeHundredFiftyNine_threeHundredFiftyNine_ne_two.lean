/-
  Brockian/CosTraceNormThreeHundredFiftyNine.lean — spectral generator at p = 359.

  [ℚ(2 cos 2π/359):ℚ] = 179 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormThreeHundredFiftyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_threeHundredFiftyNine : Nat.Prime 359 := by decide

theorem threeHundredFiftyNine_ne_two : (359 : ℕ) ≠ 2 := by decide

theorem degree_threeHundredFiftyNine : (minpoly ℚ (spectralGen 359)).natDegree = 179 :=
  real_subfield_degree prime_threeHundredFiftyNine threeHundredFiftyNine_ne_two

theorem isIntegral_spectralGen_threeHundredFiftyNine : IsIntegral ℤ (spectralGen 359) :=
  isIntegral_spectralGen prime_threeHundredFiftyNine

theorem isIntegral_spectralGen_threeHundredFiftyNine_Q : IsIntegral ℚ (spectralGen 359) :=
  isIntegral_spectralGen_ℚ prime_threeHundredFiftyNine

theorem isIntegral_and_degree_threeHundredFiftyNine :
    IsIntegral ℤ (spectralGen 359) ∧
      (minpoly ℚ (spectralGen 359)).natDegree = 179 :=
  ⟨isIntegral_spectralGen_threeHundredFiftyNine, degree_threeHundredFiftyNine⟩

theorem threeHundredFiftyNine_pack :
    IsIntegral ℤ (spectralGen 359) ∧
      (minpoly ℚ (spectralGen 359)).natDegree = 179 :=
  isIntegral_and_degree_threeHundredFiftyNine

end Brockian.CosTraceNormThreeHundredFiftyNine
