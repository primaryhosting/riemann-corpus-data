/-
  Brockian/CosTraceNormOneHundredThirtyNine.lean — spectral generator at p = 139.

  [ℚ(2 cos 2π/139):ℚ] = 69 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormOneHundredThirtyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_oneHundredThirtyNine : Nat.Prime 139 := by decide

theorem oneHundredThirtyNine_ne_two : (139 : ℕ) ≠ 2 := by decide

theorem degree_oneHundredThirtyNine : (minpoly ℚ (spectralGen 139)).natDegree = 69 :=
  real_subfield_degree prime_oneHundredThirtyNine oneHundredThirtyNine_ne_two

theorem isIntegral_spectralGen_oneHundredThirtyNine : IsIntegral ℤ (spectralGen 139) :=
  isIntegral_spectralGen prime_oneHundredThirtyNine

theorem isIntegral_spectralGen_oneHundredThirtyNine_Q : IsIntegral ℚ (spectralGen 139) :=
  isIntegral_spectralGen_ℚ prime_oneHundredThirtyNine

theorem isIntegral_and_degree_oneHundredThirtyNine :
    IsIntegral ℤ (spectralGen 139) ∧
      (minpoly ℚ (spectralGen 139)).natDegree = 69 :=
  ⟨isIntegral_spectralGen_oneHundredThirtyNine, degree_oneHundredThirtyNine⟩

theorem oneHundredThirtyNine_pack :
    IsIntegral ℤ (spectralGen 139) ∧
      (minpoly ℚ (spectralGen 139)).natDegree = 69 :=
  isIntegral_and_degree_oneHundredThirtyNine

end Brockian.CosTraceNormOneHundredThirtyNine
