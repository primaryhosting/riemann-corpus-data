/-
  Brockian/CosTraceNormOneHundredFiftyOne.lean — spectral generator at p = 151.

  [ℚ(2 cos 2π/151):ℚ] = 75 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormOneHundredFiftyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredFiftyOne : Nat.Prime 151 := by decide

theorem oneHundredFiftyOne_ne_two : (151 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredFiftyOne : (minpoly ℚ (spectralGen 151)).natDegree = 75 :=
  real_subfield_degree prime_oneHundredFiftyOne oneHundredFiftyOne_ne_two

theorem isIntegral_spectralGen_oneHundredFiftyOne : IsIntegral ℤ (spectralGen 151) :=
  isIntegral_spectralGen prime_oneHundredFiftyOne

theorem isIntegral_spectralGen_oneHundredFiftyOne_Q : IsIntegral ℚ (spectralGen 151) :=
  isIntegral_spectralGen_ℚ prime_oneHundredFiftyOne

theorem isIntegral_and_degree_oneHundredFiftyOne :
    IsIntegral ℤ (spectralGen 151) ∧
      (minpoly ℚ (spectralGen 151)).natDegree = 75 :=
  ⟨isIntegral_spectralGen_oneHundredFiftyOne, degree_oneHundredFiftyOne⟩

theorem oneHundredFiftyOne_pack :
    IsIntegral ℤ (spectralGen 151) ∧
      (minpoly ℚ (spectralGen 151)).natDegree = 75 :=
  isIntegral_and_degree_oneHundredFiftyOne

end Brockian.CosTraceNormOneHundredFiftyOne
