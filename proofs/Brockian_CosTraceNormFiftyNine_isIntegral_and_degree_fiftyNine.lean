/-
  Brockian/CosTraceNormFiftyNine.lean — spectral generator at p = 59.

  [ℚ(2 cos 2π/59):ℚ] = 29 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

namespace Brockian.CosTraceNormFiftyNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_fiftyNine : Nat.Prime 59 := by decide

theorem fiftyNine_ne_two : (59 : ℕ) ≠ 2 := by decide

theorem degree_fiftyNine : (minpoly ℚ (spectralGen 59)).natDegree = 29 :=
  real_subfield_degree prime_fiftyNine fiftyNine_ne_two

theorem isIntegral_spectralGen_fiftyNine : IsIntegral ℤ (spectralGen 59) :=
  isIntegral_spectralGen prime_fiftyNine

theorem isIntegral_spectralGen_fiftyNine_Q : IsIntegral ℚ (spectralGen 59) :=
  isIntegral_spectralGen_ℚ prime_fiftyNine

theorem isIntegral_and_degree_fiftyNine :
    IsIntegral ℤ (spectralGen 59) ∧
      (minpoly ℚ (spectralGen 59)).natDegree = 29 :=
  ⟨isIntegral_spectralGen_fiftyNine, degree_fiftyNine⟩

theorem fiftyNine_pack :
    IsIntegral ℤ (spectralGen 59) ∧
      (minpoly ℚ (spectralGen 59)).natDegree = 29 :=
  isIntegral_and_degree_fiftyNine

end Brockian.CosTraceNormFiftyNine
