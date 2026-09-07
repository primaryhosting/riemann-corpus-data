/-
  Brockian/CosTraceNormFortyOne.lean — spectral generator at p = 41.

  [ℚ(2 cos 2π/41):ℚ] = 20 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormFortyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fortyOne : Nat.Prime 41 := by decide

theorem fortyOne_ne_two : (41 : ℕ) ≠ 2 := by decide

theorem degree_fortyOne : (minpoly ℚ (spectralGen 41)).natDegree = 20 :=
  real_subfield_degree prime_fortyOne fortyOne_ne_two

theorem isIntegral_spectralGen_fortyOne : IsIntegral ℤ (spectralGen 41) :=
  isIntegral_spectralGen prime_fortyOne

theorem isIntegral_spectralGen_fortyOne_Q : IsIntegral ℚ (spectralGen 41) :=
  isIntegral_spectralGen_ℚ prime_fortyOne

theorem isIntegral_and_degree_fortyOne :
    IsIntegral ℤ (spectralGen 41) ∧
      (minpoly ℚ (spectralGen 41)).natDegree = 20 :=
  ⟨isIntegral_spectralGen_fortyOne, degree_fortyOne⟩

theorem fortyOne_pack :
    IsIntegral ℤ (spectralGen 41) ∧
      (minpoly ℚ (spectralGen 41)).natDegree = 20 :=
  isIntegral_and_degree_fortyOne

end Brockian.CosTraceNormFortyOne
