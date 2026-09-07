/-
  Brockian/CosTraceNormNineHundredEleven.lean — spectral generator at p = 911.

  [ℚ(2 cos 2π/911):ℚ] = 455 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormNineHundredEleven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_nineHundredEleven : Nat.Prime 911 := by decide

theorem nineHundredEleven_ne_two : (911 : ℕ) ≠ 2 := by decide

theorem degree_nineHundredEleven : (minpoly ℚ (spectralGen 911)).natDegree = 455 :=
  real_subfield_degree prime_nineHundredEleven nineHundredEleven_ne_two

theorem isIntegral_spectralGen_nineHundredEleven : IsIntegral ℤ (spectralGen 911) :=
  isIntegral_spectralGen prime_nineHundredEleven

theorem isIntegral_spectralGen_nineHundredEleven_Q : IsIntegral ℚ (spectralGen 911) :=
  isIntegral_spectralGen_ℚ prime_nineHundredEleven

theorem isIntegral_and_degree_nineHundredEleven :
    IsIntegral ℤ (spectralGen 911) ∧
      (minpoly ℚ (spectralGen 911)).natDegree = 455 :=
  ⟨isIntegral_spectralGen_nineHundredEleven, degree_nineHundredEleven⟩

theorem nineHundredEleven_pack :
    IsIntegral ℤ (spectralGen 911) ∧
      (minpoly ℚ (spectralGen 911)).natDegree = 455 :=
  isIntegral_and_degree_nineHundredEleven

end Brockian.CosTraceNormNineHundredEleven
