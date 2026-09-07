/-
  Brockian/CosTraceNormNineHundredSeven.lean — spectral generator at p = 907.

  [ℚ(2 cos 2π/907):ℚ] = 453 via GaloisGeneralDegree. Integrality via CosAlgebraicInteger.
  HONEST: no expanded classical monic polynomial claimed here.
-/
import Mathlib
import Brockian.CosAlgebraicInteger
import Brockian.GaloisGeneralDegree
import Brockian.GaloisWhyFive

-- decide Nat.Prime p needs higher rec depth for p ≳ 163 under AXLE
set_option maxRecDepth 10000

namespace Brockian.CosTraceNormNineHundredSeven

open Polynomial IntermediateField Algebra
open Brockian.GaloisWhyFive
open Brockian.GaloisGeneralDegree
open Brockian.CosAlgebraicInteger

theorem prime_nineHundredSeven : Nat.Prime 907 := by decide

theorem nineHundredSeven_ne_two : (907 : ℕ) ≠ 2 := by decide

theorem degree_nineHundredSeven : (minpoly ℚ (spectralGen 907)).natDegree = 453 :=
  real_subfield_degree prime_nineHundredSeven nineHundredSeven_ne_two

theorem isIntegral_spectralGen_nineHundredSeven : IsIntegral ℤ (spectralGen 907) :=
  isIntegral_spectralGen prime_nineHundredSeven

theorem isIntegral_spectralGen_nineHundredSeven_Q : IsIntegral ℚ (spectralGen 907) :=
  isIntegral_spectralGen_ℚ prime_nineHundredSeven

theorem isIntegral_and_degree_nineHundredSeven :
    IsIntegral ℤ (spectralGen 907) ∧
      (minpoly ℚ (spectralGen 907)).natDegree = 453 :=
  ⟨isIntegral_spectralGen_nineHundredSeven, degree_nineHundredSeven⟩

theorem nineHundredSeven_pack :
    IsIntegral ℤ (spectralGen 907) ∧
      (minpoly ℚ (spectralGen 907)).natDegree = 453 :=
  isIntegral_and_degree_nineHundredSeven

end Brockian.CosTraceNormNineHundredSeven
