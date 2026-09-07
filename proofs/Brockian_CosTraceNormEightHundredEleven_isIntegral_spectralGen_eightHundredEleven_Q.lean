/-
  Brockian/CosTraceNormEightHundredEleven.lean — spectral generator at p = 811.

  [ℚ(2 cos 2π/811):ℚ] = 405 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormEightHundredEleven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_eightHundredEleven : Nat.Prime 811 := by decide

theorem eightHundredEleven_ne_two : (811 : ℕ) ≠ 2 := by decide

theorem degree_eightHundredEleven : (minpoly ℚ (spectralGen 811)).natDegree = 405 :=
  real_subfield_degree prime_eightHundredEleven eightHundredEleven_ne_two

theorem isIntegral_spectralGen_eightHundredEleven : IsIntegral ℤ (spectralGen 811) :=
  isIntegral_spectralGen prime_eightHundredEleven

theorem isIntegral_spectralGen_eightHundredEleven_Q : IsIntegral ℚ (spectralGen 811) :=
  isIntegral_spectralGen_ℚ prime_eightHundredEleven

theorem isIntegral_and_degree_eightHundredEleven :
    IsIntegral ℤ (spectralGen 811) ∧
      (minpoly ℚ (spectralGen 811)).natDegree = 405 :=
  ⟨isIntegral_spectralGen_eightHundredEleven, degree_eightHundredEleven⟩

theorem eightHundredEleven_pack :
    IsIntegral ℤ (spectralGen 811) ∧
      (minpoly ℚ (spectralGen 811)).natDegree = 405 :=
  isIntegral_and_degree_eightHundredEleven

end Brockian.CosTraceNormEightHundredEleven
