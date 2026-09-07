/-
  Brockian/CosTraceNormOneHundredThirtyOne.lean — spectral generator at p = 131.

  [ℚ(2 cos 2π/131):ℚ] = 65 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormOneHundredThirtyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredThirtyOne : Nat.Prime 131 := by decide

theorem oneHundredThirtyOne_ne_two : (131 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredThirtyOne : (minpoly ℚ (spectralGen 131)).natDegree = 65 :=
  real_subfield_degree prime_oneHundredThirtyOne oneHundredThirtyOne_ne_two

theorem isIntegral_spectralGen_oneHundredThirtyOne : IsIntegral ℤ (spectralGen 131) :=
  isIntegral_spectralGen prime_oneHundredThirtyOne

theorem isIntegral_spectralGen_oneHundredThirtyOne_Q : IsIntegral ℚ (spectralGen 131) :=
  isIntegral_spectralGen_ℚ prime_oneHundredThirtyOne

theorem isIntegral_and_degree_oneHundredThirtyOne :
    IsIntegral ℤ (spectralGen 131) ∧
      (minpoly ℚ (spectralGen 131)).natDegree = 65 :=
  ⟨isIntegral_spectralGen_oneHundredThirtyOne, degree_oneHundredThirtyOne⟩

theorem oneHundredThirtyOne_pack :
    IsIntegral ℤ (spectralGen 131) ∧
      (minpoly ℚ (spectralGen 131)).natDegree = 65 :=
  isIntegral_and_degree_oneHundredThirtyOne

end Brockian.CosTraceNormOneHundredThirtyOne
