/-
  Brockian/CosTraceNormOneHundredNine.lean — spectral generator at p = 109.

  [ℚ(2 cos 2π/109):ℚ] = 54 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormOneHundredNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredNine : Nat.Prime 109 := by decide

theorem oneHundredNine_ne_two : (109 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredNine : (minpoly ℚ (spectralGen 109)).natDegree = 54 :=
  real_subfield_degree prime_oneHundredNine oneHundredNine_ne_two

theorem isIntegral_spectralGen_oneHundredNine : IsIntegral ℤ (spectralGen 109) :=
  isIntegral_spectralGen prime_oneHundredNine

theorem isIntegral_spectralGen_oneHundredNine_Q : IsIntegral ℚ (spectralGen 109) :=
  isIntegral_spectralGen_ℚ prime_oneHundredNine

theorem isIntegral_and_degree_oneHundredNine :
    IsIntegral ℤ (spectralGen 109) ∧
      (minpoly ℚ (spectralGen 109)).natDegree = 54 :=
  ⟨isIntegral_spectralGen_oneHundredNine, degree_oneHundredNine⟩

theorem oneHundredNine_pack :
    IsIntegral ℤ (spectralGen 109) ∧
      (minpoly ℚ (spectralGen 109)).natDegree = 54 :=
  isIntegral_and_degree_oneHundredNine

end Brockian.CosTraceNormOneHundredNine
