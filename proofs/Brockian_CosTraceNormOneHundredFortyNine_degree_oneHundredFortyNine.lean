/-
  Brockian/CosTraceNormOneHundredFortyNine.lean — spectral generator at p = 149.

  [ℚ(2 cos 2π/149):ℚ] = 74 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormOneHundredFortyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredFortyNine : Nat.Prime 149 := by decide

theorem oneHundredFortyNine_ne_two : (149 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredFortyNine : (minpoly ℚ (spectralGen 149)).natDegree = 74 :=
  real_subfield_degree prime_oneHundredFortyNine oneHundredFortyNine_ne_two

theorem isIntegral_spectralGen_oneHundredFortyNine : IsIntegral ℤ (spectralGen 149) :=
  isIntegral_spectralGen prime_oneHundredFortyNine

theorem isIntegral_spectralGen_oneHundredFortyNine_Q : IsIntegral ℚ (spectralGen 149) :=
  isIntegral_spectralGen_ℚ prime_oneHundredFortyNine

theorem isIntegral_and_degree_oneHundredFortyNine :
    IsIntegral ℤ (spectralGen 149) ∧
      (minpoly ℚ (spectralGen 149)).natDegree = 74 :=
  ⟨isIntegral_spectralGen_oneHundredFortyNine, degree_oneHundredFortyNine⟩

theorem oneHundredFortyNine_pack :
    IsIntegral ℤ (spectralGen 149) ∧
      (minpoly ℚ (spectralGen 149)).natDegree = 74 :=
  isIntegral_and_degree_oneHundredFortyNine

end Brockian.CosTraceNormOneHundredFortyNine
