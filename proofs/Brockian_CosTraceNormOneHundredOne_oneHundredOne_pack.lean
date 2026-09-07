/-
  Brockian/CosTraceNormOneHundredOne.lean — spectral generator at p = 101.

  [ℚ(2 cos 2π/101):ℚ] = 50 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormOneHundredOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredOne : Nat.Prime 101 := by decide

theorem oneHundredOne_ne_two : (101 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredOne : (minpoly ℚ (spectralGen 101)).natDegree = 50 :=
  real_subfield_degree prime_oneHundredOne oneHundredOne_ne_two

theorem isIntegral_spectralGen_oneHundredOne : IsIntegral ℤ (spectralGen 101) :=
  isIntegral_spectralGen prime_oneHundredOne

theorem isIntegral_spectralGen_oneHundredOne_Q : IsIntegral ℚ (spectralGen 101) :=
  isIntegral_spectralGen_ℚ prime_oneHundredOne

theorem isIntegral_and_degree_oneHundredOne :
    IsIntegral ℤ (spectralGen 101) ∧
      (minpoly ℚ (spectralGen 101)).natDegree = 50 :=
  ⟨isIntegral_spectralGen_oneHundredOne, degree_oneHundredOne⟩

theorem oneHundredOne_pack :
    IsIntegral ℤ (spectralGen 101) ∧
      (minpoly ℚ (spectralGen 101)).natDegree = 50 :=
  isIntegral_and_degree_oneHundredOne

end Brockian.CosTraceNormOneHundredOne
