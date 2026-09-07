/-
  Brockian/CosTraceNormSeventyOne.lean — spectral generator at p = 71.

  [ℚ(2 cos 2π/71):ℚ] = 35 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormSeventyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_seventyOne : Nat.Prime 71 := by decide

theorem seventyOne_ne_two : (71 : ℕ) ≠ 2 := by decide

theorem degree_seventyOne : (minpoly ℚ (spectralGen 71)).natDegree = 35 :=
  real_subfield_degree prime_seventyOne seventyOne_ne_two

theorem isIntegral_spectralGen_seventyOne : IsIntegral ℤ (spectralGen 71) :=
  isIntegral_spectralGen prime_seventyOne

theorem isIntegral_spectralGen_seventyOne_Q : IsIntegral ℚ (spectralGen 71) :=
  isIntegral_spectralGen_ℚ prime_seventyOne

theorem isIntegral_and_degree_seventyOne :
    IsIntegral ℤ (spectralGen 71) ∧
      (minpoly ℚ (spectralGen 71)).natDegree = 35 :=
  ⟨isIntegral_spectralGen_seventyOne, degree_seventyOne⟩

theorem seventyOne_pack :
    IsIntegral ℤ (spectralGen 71) ∧
      (minpoly ℚ (spectralGen 71)).natDegree = 35 :=
  isIntegral_and_degree_seventyOne

end Brockian.CosTraceNormSeventyOne
