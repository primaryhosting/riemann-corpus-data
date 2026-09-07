/-
  Brockian/CosTraceNormSixtyOne.lean — spectral generator at p = 61.

  [ℚ(2 cos 2π/61):ℚ] = 30 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormSixtyOne

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_sixtyOne : Nat.Prime 61 := by decide

theorem sixtyOne_ne_two : (61 : ℕ) ≠ 2 := by decide

theorem degree_sixtyOne : (minpoly ℚ (spectralGen 61)).natDegree = 30 :=
  real_subfield_degree prime_sixtyOne sixtyOne_ne_two

theorem isIntegral_spectralGen_sixtyOne : IsIntegral ℤ (spectralGen 61) :=
  isIntegral_spectralGen prime_sixtyOne

theorem isIntegral_spectralGen_sixtyOne_Q : IsIntegral ℚ (spectralGen 61) :=
  isIntegral_spectralGen_ℚ prime_sixtyOne

theorem isIntegral_and_degree_sixtyOne :
    IsIntegral ℤ (spectralGen 61) ∧
      (minpoly ℚ (spectralGen 61)).natDegree = 30 :=
  ⟨isIntegral_spectralGen_sixtyOne, degree_sixtyOne⟩

theorem sixtyOne_pack :
    IsIntegral ℤ (spectralGen 61) ∧
      (minpoly ℚ (spectralGen 61)).natDegree = 30 :=
  isIntegral_and_degree_sixtyOne

end Brockian.CosTraceNormSixtyOne
