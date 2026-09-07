/-
  Brockian/CosTraceNormEightyNine.lean — spectral generator at p = 89.

  [ℚ(2 cos 2π/89):ℚ] = 44 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormEightyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_eightyNine : Nat.Prime 89 := by decide

theorem eightyNine_ne_two : (89 : ℕ) ≠ 2 := by decide

theorem degree_eightyNine : (minpoly ℚ (spectralGen 89)).natDegree = 44 :=
  real_subfield_degree prime_eightyNine eightyNine_ne_two

theorem isIntegral_spectralGen_eightyNine : IsIntegral ℤ (spectralGen 89) :=
  isIntegral_spectralGen prime_eightyNine

theorem isIntegral_spectralGen_eightyNine_Q : IsIntegral ℚ (spectralGen 89) :=
  isIntegral_spectralGen_ℚ prime_eightyNine

theorem isIntegral_and_degree_eightyNine :
    IsIntegral ℤ (spectralGen 89) ∧
      (minpoly ℚ (spectralGen 89)).natDegree = 44 :=
  ⟨isIntegral_spectralGen_eightyNine, degree_eightyNine⟩

theorem eightyNine_pack :
    IsIntegral ℤ (spectralGen 89) ∧
      (minpoly ℚ (spectralGen 89)).natDegree = 44 :=
  isIntegral_and_degree_eightyNine

end Brockian.CosTraceNormEightyNine
