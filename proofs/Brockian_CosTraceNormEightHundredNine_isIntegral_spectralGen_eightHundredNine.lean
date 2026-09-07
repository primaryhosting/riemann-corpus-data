/-
  Brockian/CosTraceNormEightHundredNine.lean — spectral generator at p = 809.

  [ℚ(2 cos 2π/809):ℚ] = 404 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormEightHundredNine

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_eightHundredNine : Nat.Prime 809 := by decide

theorem eightHundredNine_ne_two : (809 : ℕ) ≠ 2 := by decide

theorem degree_eightHundredNine : (minpoly ℚ (spectralGen 809)).natDegree = 404 :=
  real_subfield_degree prime_eightHundredNine eightHundredNine_ne_two

theorem isIntegral_spectralGen_eightHundredNine : IsIntegral ℤ (spectralGen 809) :=
  isIntegral_spectralGen prime_eightHundredNine

theorem isIntegral_spectralGen_eightHundredNine_Q : IsIntegral ℚ (spectralGen 809) :=
  isIntegral_spectralGen_ℚ prime_eightHundredNine

theorem isIntegral_and_degree_eightHundredNine :
    IsIntegral ℤ (spectralGen 809) ∧
      (minpoly ℚ (spectralGen 809)).natDegree = 404 :=
  ⟨isIntegral_spectralGen_eightHundredNine, degree_eightHundredNine⟩

theorem eightHundredNine_pack :
    IsIntegral ℤ (spectralGen 809) ∧
      (minpoly ℚ (spectralGen 809)).natDegree = 404 :=
  isIntegral_and_degree_eightHundredNine

end Brockian.CosTraceNormEightHundredNine
