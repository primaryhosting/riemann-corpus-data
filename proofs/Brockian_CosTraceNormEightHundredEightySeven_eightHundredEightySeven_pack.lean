/-
  Brockian/CosTraceNormEightHundredEightySeven.lean — spectral generator at p = 887.

  [ℚ(2 cos 2π/887):ℚ] = 443 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormEightHundredEightySeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_eightHundredEightySeven : Nat.Prime 887 := by decide

theorem eightHundredEightySeven_ne_two : (887 : ℕ) ≠ 2 := by decide

theorem degree_eightHundredEightySeven : (minpoly ℚ (spectralGen 887)).natDegree = 443 :=
  real_subfield_degree prime_eightHundredEightySeven eightHundredEightySeven_ne_two

theorem isIntegral_spectralGen_eightHundredEightySeven : IsIntegral ℤ (spectralGen 887) :=
  isIntegral_spectralGen prime_eightHundredEightySeven

theorem isIntegral_spectralGen_eightHundredEightySeven_Q : IsIntegral ℚ (spectralGen 887) :=
  isIntegral_spectralGen_ℚ prime_eightHundredEightySeven

theorem isIntegral_and_degree_eightHundredEightySeven :
    IsIntegral ℤ (spectralGen 887) ∧
      (minpoly ℚ (spectralGen 887)).natDegree = 443 :=
  ⟨isIntegral_spectralGen_eightHundredEightySeven, degree_eightHundredEightySeven⟩

theorem eightHundredEightySeven_pack :
    IsIntegral ℤ (spectralGen 887) ∧
      (minpoly ℚ (spectralGen 887)).natDegree = 443 :=
  isIntegral_and_degree_eightHundredEightySeven

end Brockian.CosTraceNormEightHundredEightySeven
