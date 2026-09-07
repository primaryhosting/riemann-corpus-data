/-
  Brockian/CosTraceNormThirtyOne.lean — spectral generator at p = 31.

  [ℚ(2 cos 2π/31):ℚ] = 15 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormThirtyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_thirtyOne : Nat.Prime 31 := by decide

theorem thirtyOne_ne_two : (31 : ℕ) ≠ 2 := by decide

theorem degree_thirtyOne : (minpoly ℚ (spectralGen 31)).natDegree = 15 :=
  real_subfield_degree prime_thirtyOne thirtyOne_ne_two

theorem isIntegral_spectralGen_thirtyOne : IsIntegral ℤ (spectralGen 31) :=
  isIntegral_spectralGen prime_thirtyOne

theorem isIntegral_spectralGen_thirtyOne_Q : IsIntegral ℚ (spectralGen 31) :=
  isIntegral_spectralGen_ℚ prime_thirtyOne

theorem isIntegral_and_degree_thirtyOne :
    IsIntegral ℤ (spectralGen 31) ∧
      (minpoly ℚ (spectralGen 31)).natDegree = 15 :=
  ⟨isIntegral_spectralGen_thirtyOne, degree_thirtyOne⟩

theorem thirtyOne_pack :
    IsIntegral ℤ (spectralGen 31) ∧
      (minpoly ℚ (spectralGen 31)).natDegree = 15 :=
  isIntegral_and_degree_thirtyOne

end Brockian.CosTraceNormThirtyOne
