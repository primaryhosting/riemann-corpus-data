/-
  Brockian/CosTraceNormEightHundredSeventySeven.lean — spectral generator at p = 877.

  [ℚ(2 cos 2π/877):ℚ] = 438 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormEightHundredSeventySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_eightHundredSeventySeven : Nat.Prime 877 := by decide

theorem eightHundredSeventySeven_ne_two : (877 : ℕ) ≠ 2 := by decide

theorem degree_eightHundredSeventySeven : (minpoly ℚ (spectralGen 877)).natDegree = 438 :=
  real_subfield_degree prime_eightHundredSeventySeven eightHundredSeventySeven_ne_two

theorem isIntegral_spectralGen_eightHundredSeventySeven : IsIntegral ℤ (spectralGen 877) :=
  isIntegral_spectralGen prime_eightHundredSeventySeven

theorem isIntegral_spectralGen_eightHundredSeventySeven_Q : IsIntegral ℚ (spectralGen 877) :=
  isIntegral_spectralGen_ℚ prime_eightHundredSeventySeven

theorem isIntegral_and_degree_eightHundredSeventySeven :
    IsIntegral ℤ (spectralGen 877) ∧
      (minpoly ℚ (spectralGen 877)).natDegree = 438 :=
  ⟨isIntegral_spectralGen_eightHundredSeventySeven, degree_eightHundredSeventySeven⟩

theorem eightHundredSeventySeven_pack :
    IsIntegral ℤ (spectralGen 877) ∧
      (minpoly ℚ (spectralGen 877)).natDegree = 438 :=
  isIntegral_and_degree_eightHundredSeventySeven

end Brockian.CosTraceNormEightHundredSeventySeven
