/-
  Brockian/CosTraceNormThreeHundredFortyNine.lean — spectral generator at p = 349.

  [ℚ(2 cos 2π/349):ℚ] = 174 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormThreeHundredFortyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_threeHundredFortyNine : Nat.Prime 349 := by decide

theorem threeHundredFortyNine_ne_two : (349 : ℕ) ≠ 2 := by decide

theorem degree_threeHundredFortyNine : (minpoly ℚ (spectralGen 349)).natDegree = 174 :=
  real_subfield_degree prime_threeHundredFortyNine threeHundredFortyNine_ne_two

theorem isIntegral_spectralGen_threeHundredFortyNine : IsIntegral ℤ (spectralGen 349) :=
  isIntegral_spectralGen prime_threeHundredFortyNine

theorem isIntegral_spectralGen_threeHundredFortyNine_Q : IsIntegral ℚ (spectralGen 349) :=
  isIntegral_spectralGen_ℚ prime_threeHundredFortyNine

theorem isIntegral_and_degree_threeHundredFortyNine :
    IsIntegral ℤ (spectralGen 349) ∧
      (minpoly ℚ (spectralGen 349)).natDegree = 174 :=
  ⟨isIntegral_spectralGen_threeHundredFortyNine, degree_threeHundredFortyNine⟩

theorem threeHundredFortyNine_pack :
    IsIntegral ℤ (spectralGen 349) ∧
      (minpoly ℚ (spectralGen 349)).natDegree = 174 :=
  isIntegral_and_degree_threeHundredFortyNine

end Brockian.CosTraceNormThreeHundredFortyNine
