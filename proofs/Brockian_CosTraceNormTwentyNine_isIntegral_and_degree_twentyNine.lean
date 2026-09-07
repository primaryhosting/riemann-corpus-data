/-
  Brockian/CosTraceNormTwentyNine.lean — spectral generator at p = 29.

  [ℚ(2 cos 2π/29):ℚ] = 14 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormTwentyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_twentyNine : Nat.Prime 29 := by decide

theorem twentyNine_ne_two : (29 : ℕ) ≠ 2 := by decide

theorem degree_twentyNine : (minpoly ℚ (spectralGen 29)).natDegree = 14 :=
  real_subfield_degree prime_twentyNine twentyNine_ne_two

theorem isIntegral_spectralGen_twentyNine : IsIntegral ℤ (spectralGen 29) :=
  isIntegral_spectralGen prime_twentyNine

theorem isIntegral_spectralGen_twentyNine_Q : IsIntegral ℚ (spectralGen 29) :=
  isIntegral_spectralGen_ℚ prime_twentyNine

theorem isIntegral_and_degree_twentyNine :
    IsIntegral ℤ (spectralGen 29) ∧
      (minpoly ℚ (spectralGen 29)).natDegree = 14 :=
  ⟨isIntegral_spectralGen_twentyNine, degree_twentyNine⟩

theorem twentyNine_pack :
    IsIntegral ℤ (spectralGen 29) ∧
      (minpoly ℚ (spectralGen 29)).natDegree = 14 :=
  isIntegral_and_degree_twentyNine

end Brockian.CosTraceNormTwentyNine
