/-
  Brockian/CosTraceNormSeventyNine.lean — spectral generator at p = 79.

  [ℚ(2 cos 2π/79):ℚ] = 39 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormSeventyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_seventyNine : Nat.Prime 79 := by decide

theorem seventyNine_ne_two : (79 : ℕ) ≠ 2 := by decide

theorem degree_seventyNine : (minpoly ℚ (spectralGen 79)).natDegree = 39 :=
  real_subfield_degree prime_seventyNine seventyNine_ne_two

theorem isIntegral_spectralGen_seventyNine : IsIntegral ℤ (spectralGen 79) :=
  isIntegral_spectralGen prime_seventyNine

theorem isIntegral_spectralGen_seventyNine_Q : IsIntegral ℚ (spectralGen 79) :=
  isIntegral_spectralGen_ℚ prime_seventyNine

theorem isIntegral_and_degree_seventyNine :
    IsIntegral ℤ (spectralGen 79) ∧
      (minpoly ℚ (spectralGen 79)).natDegree = 39 :=
  ⟨isIntegral_spectralGen_seventyNine, degree_seventyNine⟩

theorem seventyNine_pack :
    IsIntegral ℤ (spectralGen 79) ∧
      (minpoly ℚ (spectralGen 79)).natDegree = 39 :=
  isIntegral_and_degree_seventyNine

end Brockian.CosTraceNormSeventyNine
