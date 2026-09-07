/-
  Brockian/CosTraceNormOneHundredSeventyNine.lean — spectral generator at p = 179.

  [ℚ(2 cos 2π/179):ℚ] = 89 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

set_option maxRecDepth 10000

namespace Brockian.CosTraceNormOneHundredSeventyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredSeventyNine : Nat.Prime 179 := by decide

theorem oneHundredSeventyNine_ne_two : (179 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredSeventyNine : (minpoly ℚ (spectralGen 179)).natDegree = 89 :=
  real_subfield_degree prime_oneHundredSeventyNine oneHundredSeventyNine_ne_two

theorem isIntegral_spectralGen_oneHundredSeventyNine : IsIntegral ℤ (spectralGen 179) :=
  isIntegral_spectralGen prime_oneHundredSeventyNine

theorem isIntegral_spectralGen_oneHundredSeventyNine_Q : IsIntegral ℚ (spectralGen 179) :=
  isIntegral_spectralGen_ℚ prime_oneHundredSeventyNine

theorem isIntegral_and_degree_oneHundredSeventyNine :
    IsIntegral ℤ (spectralGen 179) ∧
      (minpoly ℚ (spectralGen 179)).natDegree = 89 :=
  ⟨isIntegral_spectralGen_oneHundredSeventyNine, degree_oneHundredSeventyNine⟩

theorem oneHundredSeventyNine_pack :
    IsIntegral ℤ (spectralGen 179) ∧
      (minpoly ℚ (spectralGen 179)).natDegree = 89 :=
  isIntegral_and_degree_oneHundredSeventyNine

end Brockian.CosTraceNormOneHundredSeventyNine
